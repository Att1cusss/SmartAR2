import re
from collections import deque
from typing import List, Tuple

from slither.analyses.data_dependency.data_dependency import get_dependencies_ssa
from slither.core.cfg.node import NodeType
from slither.core.declarations import FunctionContract
from slither.core.declarations.solidity_variables import SOLIDITY_VARIABLES_COMPOSED
from slither.core.solidity_types.elementary_type import Uint, Int, Max_Uint, Max_Int, Min_Int, Min_Uint
from slither.slithir.operations import Index, SolidityCall, Assignment, Binary, Phi
from slither.slithir.variables import Constant, ReferenceVariable
from z3 import BitVec, UGE, ULE, Bool, Or, And, UGT, ULT, is_bv, is_bool, Solver, sat, unsat

from utils.compile import change_solc_version_to, read_source_code, build_slither, build_ast, compile_contract
from utils.entity.ExpressionTree import build_if_expression_tree, build_require_assert_expression_tree
from utils.locate import RepairTarget, locate_repair_targets

untrusted = {
    "block.basefee",
    "block.coinbase",
    "block.difficulty",
    "block.prevrandao",
    "block.gaslimit",
    "block.timestamp",
    "block.blockhash",
    "block.chainid",
    "msg.data",
    "msg.gas",
    "msg.sender",
    "msg.sig",
    "msg.value",
    "tx.gasprice",
    "tx.origin",
    "chain.id",
    "block.prevhash",
    "self.balance",
}

trusted = {
    "block.number": 20430475,
    "now": 1722566453
}


class FalsePositiveRecognizer:
    def __init__(self, repair_targets: List[RepairTarget]):
        self.repair_targets = repair_targets
        self.constants = {}
        self.referenced_obj_of = {}
        self.final_reference_of = {}
        self.z3v_of = {}
        self.type_constrains_of = {}

    def recognize_true_positive(self):
        true_positive_targets = {target: True for target in self.repair_targets}
        false_positive_targets = {}
        for target in true_positive_targets:
            if true_positive_targets[target] is False:
                continue
            try:
                if self.anti_pattern_one_assignment(target):
                    true_positive_targets[target] = False
                    false_positive_targets[target] = 'safe_range'
            except Exception as e:
                pass
            try:
                if true_positive_targets[target] is True and self.anti_pattern_safe_check(target):
                    true_positive_targets[target] = False
                    false_positive_targets[target] = 'safe_check'
            except Exception as e:
                pass
            try:
                if true_positive_targets[target] is True and self.anti_pattern_invariant_check(target):
                    true_positive_targets[target] = False
                    false_positive_targets[target] = 'invariant_check'
            except Exception as e:
                pass
            try:
                if true_positive_targets[target] is True and self.anti_pattern_context_constrain(target):
                    true_positive_targets[target] = False
                    false_positive_targets[target] = 'context_constrain'
            except Exception as e:
                pass
        return {target for target, is_true in true_positive_targets.items() if is_true}, false_positive_targets

    @staticmethod
    def anti_pattern_safe_range(repair_target: RepairTarget) -> bool:
        lv_safe = False
        rv_safe = False
        lv = repair_target.ir.variable_left
        rv = repair_target.ir.variable_right
        if isinstance(lv, Constant):
            lv_safe = True
        if isinstance(rv, Constant):
            rv_safe = True
        ddg = {}
        ssas = set()
        if not lv_safe:
            ddg[lv] = set()
            ssas.add(lv)
        if not rv_safe:
            ddg[rv] = set()
            ssas.add(rv)
        add_new_node = True
        while add_new_node:
            add_new_node = False
            for ssa in ssas:
                dependencies = get_dependencies_ssa(variable=ssa, context=repair_target.slither_function_node.contract)
                for dependency in dependencies:
                    ddg[ssa].add(dependency)
                    if dependency not in ddg:
                        ddg[dependency] = set()
            if ddg.keys() != ssas:
                add_new_node = True
                ssas = set(ddg.keys())
        deleted_ssas = set()
        out_degrees = {ssa: 0 for ssa in ssas}
        queue = deque()
        for src in ddg:
            for dest in ddg[src]:
                out_degrees[src] += 1
        for ssa in ssas:
            if out_degrees[ssa] == 0 and (
                    ssa.name == "now" or ssa.name == "block.number" or ssa.name not in SOLIDITY_VARIABLES_COMPOSED):
                deleted_ssas.add(ssa)
                queue.append(ssa)
        while len(queue) != 0:
            ssa = queue.popleft()
            if len(ddg[ssa]) == 0 and (
                    ssa.name == "now" or ssa.name == "block.number" or ssa.name not in SOLIDITY_VARIABLES_COMPOSED):
                for src in ddg:
                    for dest in ddg[src]:
                        if dest == ssa:
                            out_degrees[src] -= 1
                            if out_degrees[src] == 0:
                                deleted_ssas.add(src)
                                queue.append(src)
            else:
                dependency_all_deleted = True
                for dependency in ddg[ssa]:
                    if dependency not in deleted_ssas:
                        dependency_all_deleted = False
                if dependency_all_deleted:
                    for src in ddg:
                        for dest in ddg[src]:
                            if dest == ssa:
                                out_degrees[src] -= 1
                                if out_degrees[src] == 0:
                                    deleted_ssas.add(src)
                                    queue.append(src)
        if lv in deleted_ssas:
            lv_safe = True
        if rv in deleted_ssas:
            rv_safe = True
        return lv_safe and rv_safe

    @staticmethod
    def anti_pattern_safe_check(repair_target: RepairTarget) -> bool:
        fp = False
        expression = repair_target.slither_statement_node.source_mapping.content
        reference_of_ir_variable = {}
        for ir in repair_target.slither_statement_node.irs_ssa:
            if isinstance(ir, Index):
                reference_of_ir_variable[ir.lvalue.name] = ir.variable_left.name + '[' + ir.variable_right.name + ']'
        if repair_target.ir.variable_left.name in reference_of_ir_variable:
            a_escaped = re.escape(reference_of_ir_variable[repair_target.ir.variable_left.name])
        else:
            a_escaped = re.escape(repair_target.ir.variable_left.name)
        if repair_target.ir.variable_right.name in reference_of_ir_variable:
            b_escaped = re.escape(reference_of_ir_variable[repair_target.ir.variable_right.name])
        else:
            b_escaped = re.escape(repair_target.ir.variable_right.name)
        pattern = re.compile(
            fr"(\b{a_escaped}\s*[+\-*/]\s*{b_escaped}\s*(?:>=|<=|>|<)\s*({a_escaped}|{b_escaped})|({a_escaped}|{b_escaped})\s*(?:>=|<=|>|<)\s*{a_escaped}\s*[+\-*/]\s*{b_escaped})"
        )
        fp = pattern.search(expression) is not None
        return fp

    def anti_pattern_one_assignment(self, repair_target: RepairTarget) -> bool:
        fp = False
        lv_constant = False
        rv_constant = False
        lv = 0
        rv = 0
        if repair_target.ir.variable_left.name in untrusted or repair_target.ir.variable_right.name in untrusted:
            return False
        for variable in repair_target.slither_function_node.parameters:
            if repair_target.ir.variable_left.name == variable.name or repair_target.ir.variable_right.name == variable:
                return False
        if repair_target.ir.variable_left.name in trusted:
            lv_constant = True
            lv = trusted[repair_target.ir.variable_left.name]
        elif repair_target.ir.variable_left.name[0].isdigit():
            lv_constant = True
            lv = eval(repair_target.ir.variable_left.name)
        elif repair_target.ir.variable_left.name in self.constants:
            lv_constant = True
            lv = self.constants[repair_target.ir.variable_left.name]

        if repair_target.ir.variable_right.name in trusted:
            rv_constant = True
            rv = trusted[repair_target.ir.variable_right.name]
        elif repair_target.ir.variable_right.name[0].isdigit():
            rv_constant = True
            rv = eval(repair_target.ir.variable_right.name)
        elif repair_target.ir.variable_right.name in self.constants:
            rv_constant = True
            rv = self.constants[repair_target.ir.variable_right.name]

        lv_assignments = set()
        rv_assignments = set()
        for state_variable in repair_target.slither_function_node.contract.state_variables_declared:
            if state_variable.name == repair_target.ir.variable_left.name and state_variable.expression is not None:
                lv_assignments.add(str(state_variable.expression))
            if state_variable.name == repair_target.ir.variable_right.name and state_variable.expression is not None:
                rv_assignments.add(str(state_variable.expression))
        for function in repair_target.slither_function_node.contract.functions:
            for node in function.nodes:
                if node.type == NodeType.EXPRESSION:
                    for variable in node.variables_written:
                        if variable.name == repair_target.ir.variable_left.name:
                            for v in node.variables_read:
                                lv_assignments.add(v.name)
                        if variable.name == repair_target.ir.variable_right.name:
                            for v in node.variables_read:
                                rv_assignments.add(v.name)
        if len(lv_assignments) == 1 and list(lv_assignments)[0] in trusted:
            lv_constant = True
            lv = trusted[list(lv_assignments)[0]]
        elif len(lv_assignments) == 1 and list(lv_assignments)[0][0].isdigit():
            lv_constant = True
            lv = eval(repair_target.ir.variable_left.name)

        if len(rv_assignments) == 1 and list(rv_assignments)[0] in trusted:
            rv_constant = True
            rv = trusted[list(rv_assignments)[0]]
        elif len(rv_assignments) == 1 and list(rv_assignments)[0][0].isdigit():
            rv_constant = True
            rv = eval(repair_target.ir.variable_right.name)

        safe_check = False
        op = repair_target.ir.type_str
        operand_type = str(repair_target.ir.variable_right.type)
        res = 0
        if operand_type in Uint:
            if op == '+':
                safe_check = Min_Uint[operand_type] <= lv + rv <= Max_Uint[operand_type]
                res = lv + rv
            elif op == '-':
                safe_check = Min_Uint[operand_type] <= lv - rv <= Max_Uint[operand_type]
                res = lv - rv
            elif op == '*':
                safe_check = Min_Uint[operand_type] <= lv * rv <= Max_Uint[operand_type]
                res = lv * rv
            elif op == '/':
                safe_check = rv != 0
                if rv != 0:
                    res = lv / rv
        elif operand_type in Int:
            if op == '+':
                safe_check = Min_Int[operand_type] <= lv + rv <= Max_Int[operand_type]
                res = lv + rv
            elif op == '-':
                safe_check = Min_Int[operand_type] <= lv - rv <= Max_Int[operand_type]
                res = lv - rv
            elif op == '*':
                safe_check = Min_Int[operand_type] <= lv * rv <= Max_Int[operand_type]
                res = lv * rv
            elif op == '/':
                safe_check = rv != 0
                if rv != 0:
                    res = lv / rv
        fp = lv_constant and rv_constant and safe_check
        if fp:
            self.constants[repair_target.ir.lvalue.name] = res
        return fp

    def anti_pattern_context_constrain(self, repair_target: RepairTarget) -> bool:
        constrains = []
        for node in repair_target.slither_function_node.nodes:
            for ssa in node.irs_ssa:
                if isinstance(ssa, Index):
                    ssa: Index
                    self.referenced_obj_of[ssa.lvalue] = {}
                    self.referenced_obj_of[ssa.lvalue]['left'] = ssa.variable_left
                    self.referenced_obj_of[ssa.lvalue]['right'] = ssa.variable_right
        for ref in self.referenced_obj_of:
            self.final_reference_of[str(ref)] = str(self.get_final_reference(ref))
        dominators = self.calculate_dominators(repair_target.slither_function_node)
        post_dominators = self.calculate_post_dominators(repair_target.slither_function_node)
        if_nodes = {}
        assert_bool_nodes = set()
        require_bool_nodes = set()
        require_bool_string_nodes = set()
        node_of_id = {}
        for node in repair_target.slither_function_node.nodes:
            node_of_id[node.node_id] = node
        for node_id in dominators[repair_target.slither_statement_node.node_id]:
            if node_of_id[node_id].type == NodeType.IF and node_of_id[node_id].son_true.node_id in dominators[repair_target.slither_statement_node.node_id]:
                if_nodes[node_of_id[node_id]] = True
            elif node_of_id[node_id].type == NodeType.IFLOOP and node_of_id[node_id].son_true.node_id in dominators[repair_target.slither_statement_node.node_id]:
                if_nodes[node_of_id[node_id]] = True
            elif node_of_id[node_id].type == NodeType.IF and node_of_id[node_id].son_false.node_id in dominators[repair_target.slither_statement_node.node_id]:
                if_nodes[node_of_id[node_id]] = False
            elif node_of_id[node_id].type == NodeType.IFLOOP and node_of_id[node_id].son_false.node_id in dominators[repair_target.slither_statement_node.node_id]:
                if_nodes[node_of_id[node_id]] = False
            elif node_of_id[node_id].type == NodeType.EXPRESSION and \
                    len(node_of_id[node_id].irs_ssa) > 0 and \
                    isinstance(node_of_id[node_id].irs_ssa[-1], SolidityCall):
                if node_of_id[node_id].irs_ssa[-1].function.name == 'assert(bool)':
                    assert_bool_nodes.add(node_of_id[node_id])
                elif node_of_id[node_id].irs_ssa[-1].function.name == 'require(bool)':
                    require_bool_nodes.add(node_of_id[node_id])
                elif node_of_id[node_id].irs_ssa[-1].function.name == 'require(bool,string)':
                    require_bool_string_nodes.add(node_of_id[node_id])
        for node_id in post_dominators[repair_target.slither_statement_node.node_id]:
            if node_id == -1:
                continue
            if node_of_id[node_id].type == NodeType.EXPRESSION and \
                    len(node_of_id[node_id].irs_ssa) > 0 and \
                    isinstance(node_of_id[node_id].irs_ssa[-1], SolidityCall):
                if node_of_id[node_id].irs_ssa[-1].function.name == 'assert(bool)':
                    assert_bool_nodes.add(node_of_id[node_id])
                elif node_of_id[node_id].irs_ssa[-1].function.name == 'require(bool)':
                    require_bool_nodes.add(node_of_id[node_id])
                elif node_of_id[node_id].irs_ssa[-1].function.name == 'require(bool,string)':
                    require_bool_string_nodes.add(node_of_id[node_id])

        repair_target_variables = set()
        if str(repair_target.ir.variable_left) in self.final_reference_of:
            lv = self.final_reference_of[str(repair_target.ir.variable_left)]
            repair_target_variables.add(lv)
            constrains.extend(self.register_z3v_semi(lv, str(repair_target.ir.variable_left.type)))
        elif isinstance(repair_target.ir.variable_left, ReferenceVariable):
            lv = str(repair_target.ir.variable_left.points_to_origin)
            repair_target_variables.add(lv)
            constrains.extend(self.register_z3v_semi(lv, str(repair_target.ir.variable_left.type)))
        else:
            lv = str(repair_target.ir.variable_left)
            repair_target_variables.add(lv)
            constrains.extend(self.register_z3v_semi(lv, str(repair_target.ir.variable_left.type)))
        if str(repair_target.ir.variable_right) in self.final_reference_of:
            rv = self.final_reference_of[str(repair_target.ir.variable_right)]
            repair_target_variables.add(rv)
            constrains.extend(self.register_z3v_semi(rv, str(repair_target.ir.variable_right.type)))
        elif isinstance(repair_target.ir.variable_right, ReferenceVariable):
            rv = str(repair_target.ir.variable_right.points_to_origin)
            repair_target_variables.add(rv)
            constrains.extend(self.register_z3v_semi(rv, str(repair_target.ir.variable_right.type)))
        else:
            rv = str(repair_target.ir.variable_right)
            repair_target_variables.add(rv)
            constrains.extend(self.register_z3v_semi(rv, str(repair_target.ir.variable_right.type)))
        for ir in repair_target.slither_statement_node.irs_ssa:
            if isinstance(ir, Binary) and 'TMP' in ir.lvalue.name:
                constrains.extend(self.parse_binary_ir(ir))
            if isinstance(ir, Assignment):
                constrains.extend(self.parse_assignment_ir(ir))

        for if_node in if_nodes:
            tree_root = build_if_expression_tree(if_node)
            if tree_root is None:
                continue
            for ir in if_node.irs_ssa:
                if isinstance(ir, Binary):
                    constrains.extend(self.parse_binary_ir(ir))
                elif isinstance(ir, Assignment):
                    constrains.extend(self.parse_assignment_ir(ir))
            if str(tree_root.variable) in self.z3v_of:
                constrains.append(self.z3v_of[str(tree_root.variable)] == if_nodes[if_node])
        for require_bool_node in require_bool_nodes:
            tree_root = build_require_assert_expression_tree(require_bool_node)
            if tree_root is None:
                continue
            for ir in require_bool_node.irs_ssa:
                if isinstance(ir, Binary):
                    constrains.extend(self.parse_binary_ir(ir))
                elif isinstance(ir, Assignment):
                    constrains.extend(self.parse_assignment_ir(ir))
            if str(tree_root.variable) in self.z3v_of:
                constrains.append(self.z3v_of[str(tree_root.variable)] == True)
        for require_bool_string_node in require_bool_string_nodes:
            tree_root = build_require_assert_expression_tree(require_bool_string_node)
            if tree_root is None:
                continue
            for ir in require_bool_string_node.irs_ssa:
                if isinstance(ir, Binary):
                    constrains.extend(self.parse_binary_ir(ir))
                elif isinstance(ir, Assignment):
                    constrains.extend(self.parse_assignment_ir(ir))
            if str(tree_root.variable) in self.z3v_of:
                constrains.append(self.z3v_of[str(tree_root.variable)] == True)
        for assert_bool_node in assert_bool_nodes:
            tree_root = build_require_assert_expression_tree(assert_bool_node)
            if tree_root is None:
                continue
            for ir in assert_bool_node.irs_ssa:
                if isinstance(ir, Binary):
                    constrains.extend(self.parse_binary_ir(ir))
                elif isinstance(ir, Assignment):
                    constrains.extend(self.parse_assignment_ir(ir))
            if str(tree_root.variable) in self.z3v_of:
                constrains.append(self.z3v_of[str(tree_root.variable)] == True)
        for node in repair_target.slither_function_node.nodes:
            for ir in node.irs_ssa:
                if isinstance(ir, Phi) and len(ir.rvalues) == 1:
                    constrains.extend(self.parse_phi(ir))
        safe = False
        solver = Solver()
        solver.set("timeout", 30000)
        solver.add(constrains)
        a = self.z3v_of[lv]
        b = self.z3v_of[rv]
        tp = str(repair_target.ir.variable_left.type)
        if repair_target.ir.type_str == '+':
            if str(repair_target.ir.variable_left.type) in Uint:
                overflow_condition = UGT(a + b, Max_Uint[tp])
                not_overflow_condition = ULE(a + b, Max_Uint[tp])
                if solver.check(overflow_condition) == unsat and solver.check(not_overflow_condition) == sat:
                    safe = True
                else:
                    pass
            else:
                overflow_condition = Or([And([a > 0, b > 0, a + b <= a]), And([a < 0, b < 0, a + b >= a])])
                not_overflow_condition = Or([And([a > 0, b > 0, a + b > a]), And([a < 0, b < 0, a + b < a])])
                if solver.check(overflow_condition) == unsat and solver.check(not_overflow_condition) == sat:
                    safe = True
                else:
                    pass
        elif repair_target.ir.type_str == '-':
            if str(repair_target.ir.variable_left.type) in Uint:
                overflow_condition = UGT(b, a)
                not_overflow_condition = UGE(a, b)
                if solver.check(overflow_condition) == unsat and solver.check(not_overflow_condition) == sat:
                    safe = True
                else:
                    pass
            else:
                overflow_condition = Or([And([a > 0, b < 0, a - b <= a]), And([a < 0, b > 0, a - b >= a])])
                not_overflow_condition = Or([And([a > 0, b < 0, a - b > a]), And([a < 0, b > 0, a - b < a])])
                if solver.check(overflow_condition) == unsat and solver.check(not_overflow_condition) == sat:
                    safe = True
                else:
                    pass
        elif repair_target.ir.type_str == '*':
            overflow_condition = UGT(a * b, Max_Uint[tp])
            not_overflow_condition = ULE(a * b, Max_Uint[tp])
            if solver.check(overflow_condition) == unsat:
                safe = True
            else:
                pass
        elif repair_target.ir.type_str == '/':
            overflow_condition = b == 0
            not_overflow_condition = b != 0
            if solver.check(overflow_condition) == unsat and solver.check(not_overflow_condition) == sat:
                safe = True
            else:
                pass
        return safe

    def register_z3v_semi(self, variable_name: str, tp: str):
        if variable_name in self.z3v_of:
            if variable_name in self.type_constrains_of:
                return [self.type_constrains_of[variable_name]]
            else:
                return []
        constrains = []
        if tp in Uint:
            self.z3v_of[variable_name] = BitVec(name=variable_name, bv=260)
            if variable_name.isnumeric():
                constrains.append(self.z3v_of[variable_name] == int(variable_name))
            else:
                constrains.append(UGE(self.z3v_of[variable_name], Min_Uint[tp]))
                constrains.append(ULE(self.z3v_of[variable_name], Max_Uint[tp]))
        elif tp in Int:
            self.z3v_of[variable_name] = BitVec(name=variable_name, bv=260)
            if variable_name.isnumeric():
                constrains.append(self.z3v_of[variable_name] == int(variable_name))
            else:
                constrains.append(self.z3v_of[variable_name] >= Min_Int[tp])
                constrains.append(self.z3v_of[variable_name] <= Max_Int[tp])
        elif tp == 'bool':
            self.z3v_of[variable_name] = Bool(name=variable_name)
        else:
            self.z3v_of[variable_name] = BitVec(name=variable_name, bv=260)
        self.type_constrains_of[variable_name] = And(constrains)
        return constrains

    def register_z3v_auto(self, ir_variable):
        if str(ir_variable) in self.final_reference_of:
            variable_name = self.final_reference_of[str(ir_variable)]
        elif isinstance(ir_variable, ReferenceVariable):
            variable_name = str(ir_variable.points_to_origin)
        else:
            variable_name = str(ir_variable)
        return self.register_z3v_semi(variable_name=variable_name, tp=str(ir_variable.type))

    def parse_binary_ir(self, ir: Binary) -> List:
        constrains = []

        if str(ir.lvalue) in self.final_reference_of:
            lv = self.final_reference_of[str(ir.lvalue)]
        elif isinstance(ir.lvalue, ReferenceVariable):
            lv = str(ir.lvalue.points_to_origin)
        else:
            lv = str(ir.lvalue)
        
        if str(ir.variable_left) in self.final_reference_of:
            vl = self.final_reference_of[str(ir.variable_left)]
        elif isinstance(ir.variable_left, ReferenceVariable):
            vl = str(ir.variable_left.points_to_origin)
        else:
            vl = str(ir.variable_left)
            
        if str(ir.variable_right) in self.final_reference_of:
            vr = self.final_reference_of[str(ir.variable_right)]
        elif isinstance(ir.variable_right, ReferenceVariable):
            vr = str(ir.variable_right.points_to_origin)
        else:
            vr = str(ir.variable_right)

        constrains.extend(self.register_z3v_auto(ir.lvalue))
        constrains.extend(self.register_z3v_auto(ir.variable_left))
        constrains.extend(self.register_z3v_auto(ir.variable_right))

        tp = str(ir.variable_left.type)

        if ir.type_str == '||':
            constrains.append(self.z3v_of[lv] == Or(self.z3v_of[vl], self.z3v_of[vr]))
        elif ir.type_str == '&&':
            constrains.append(self.z3v_of[lv] == And(self.z3v_of[vl], self.z3v_of[vr]))
        elif ir.type_str == '>':
            if tp in Uint:
                constrains.append(self.z3v_of[lv] == UGT(self.z3v_of[vl], self.z3v_of[vr]))
            else:
                constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] > self.z3v_of[vr]))
        elif ir.type_str == '>=':
            if tp in Uint:
                constrains.append(self.z3v_of[lv] == UGE(self.z3v_of[vl], self.z3v_of[vr]))
            else:
                constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] >= self.z3v_of[vr]))
        elif ir.type_str == '<':
            if tp in Uint:
                constrains.append(self.z3v_of[lv] == ULT(self.z3v_of[vl], self.z3v_of[vr]))
            else:
                constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] < self.z3v_of[vr]))
        elif ir.type_str == '<=':
            if tp in Uint:
                constrains.append(self.z3v_of[lv] == ULE(self.z3v_of[vl], self.z3v_of[vr]))
            else:
                constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] <= self.z3v_of[vr]))
        elif ir.type_str == '==':
            constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] == self.z3v_of[vr]))
        elif ir.type_str == '!=':
            constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] != self.z3v_of[vr]))
        elif ir.type_str == '+':
            if tp in Uint:
                constrains.append(self.z3v_of[lv] == ((self.z3v_of[vl] + self.z3v_of[vr]) % (2 ** self.get_int_bits(tp))))
            else:
                constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] + self.z3v_of[vr]))

        elif ir.type_str == '-':
            if tp in Uint:
                constrains.append(self.z3v_of[lv] == (
                        (self.z3v_of[vl] - self.z3v_of[vr] + (2 ** self.get_int_bits(tp))) % (2 ** self.get_int_bits(tp))
                ))
            else:
                constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] - self.z3v_of[vr]))

        elif ir.type_str == '*':
            if tp in Uint:
                constrains.append(self.z3v_of[lv] == ((self.z3v_of[vl] * self.z3v_of[vr]) % (2 ** self.get_int_bits(tp))))
            else:
                constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] * self.z3v_of[vr]))
        elif ir.type_str == '/':
            constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] / self.z3v_of[vr]))
        elif ir.type_str == '%':
            constrains.append(self.z3v_of[lv] == (self.z3v_of[vl] % self.z3v_of[vr]))
        elif ir.type_str == '**':
            pass
        return constrains

    def parse_assignment_ir(self, ir: Assignment) -> List:
        constrains = []
        if str(ir.lvalue) in self.final_reference_of:
            lv = self.final_reference_of[str(ir.lvalue)]
        elif isinstance(ir.lvalue, ReferenceVariable):
            lv = str(ir.lvalue.points_to_origin)
        else:
            lv = str(ir.lvalue)

        if str(ir.rvalue) in self.final_reference_of:
            rv = self.final_reference_of[str(ir.rvalue)]
        elif isinstance(ir.rvalue, ReferenceVariable):
            rv = str(ir.rvalue.points_to_origin)
        else:
            rv = str(ir.rvalue)

        constrains.extend(self.register_z3v_semi(lv, str(ir.lvalue.type)))
        constrains.extend(self.register_z3v_semi(rv, str(ir.rvalue.type)))
        constrains.append(self.z3v_of[lv] == self.z3v_of[rv])
        return constrains

    def parse_phi(self, ir: Phi):
        assert len(ir.rvalues) == 1
        constrains = []
        lv = str(ir.lvalue)
        rv = str(ir.rvalues[0])
        new_z3v_of = {}
        for var in self.z3v_of:
            var: str
            new_var = ''
            if lv in var:
                new_var = var.replace(lv, rv)
            elif rv in var:
                new_var = var.replace(rv, lv)

            if new_var != '' and new_var not in self.z3v_of:
                if is_bv(self.z3v_of[var]):
                    new_z3v_of[new_var] = BitVec(new_var, self.z3v_of[var].size())
                elif is_bool(self.z3v_of[var]):
                    new_z3v_of[new_var] = Bool(new_var)
                constrains.append(new_z3v_of[new_var] == self.z3v_of[var])
            elif new_var != '' and new_var in self.z3v_of:
                constrains.append(self.z3v_of[new_var] == self.z3v_of[var])
        for new_var in new_z3v_of:
            self.z3v_of[new_var] = new_z3v_of[new_var]
        return constrains

    def anti_pattern_invariant_check(self, repair_target: RepairTarget):
        if len(repair_target.slither_statement_node.irs_ssa) != 0 and \
                isinstance(repair_target.slither_statement_node.irs_ssa[-1], SolidityCall) and \
                repair_target.slither_statement_node.irs_ssa[-1].function.name == 'assert(bool)':
            matched, a, b, c = self.match_assert(repair_target.slither_statement_node.source_mapping.content)
            if not matched:
                return False
            dominators = self.calculate_dominators(repair_target.slither_function_node)
            for node in repair_target.slither_function_node.nodes:
                if node.node_id in dominators[repair_target.slither_statement_node.node_id] and \
                        len(node.irs_ssa) != 0 and \
                        isinstance(node.irs_ssa[-1], Assignment):
                    if self.valid_assignment(node.source_mapping.content, a, b, c):
                        return True
        if len(repair_target.slither_statement_node.irs_ssa) != 0 and \
                isinstance(repair_target.slither_statement_node.irs_ssa[-1], Assignment):
            match, a, b, c = self.match_assignment(repair_target.slither_statement_node.source_mapping.content)
            if not match:
                return False
            post_dominators = self.calculate_post_dominators(repair_target.slither_function_node)
            for node in repair_target.slither_function_node.nodes:
                if node.node_id in post_dominators[repair_target.slither_statement_node.node_id] and \
                        len(node.irs_ssa) != 0 and \
                        isinstance(node.irs_ssa[-1], SolidityCall) and node.irs_ssa[-1].function.name == 'assert(bool)':
                    if self.valid_assert(node.source_mapping.content, a, b, c):
                        return True

    def anti_pattern_random_number(self):
        pass

    def get_final_reference(self, ref):
        if ref not in self.referenced_obj_of:
            return ref
        left_ref = self.referenced_obj_of[ref]['left']
        right_ref = self.referenced_obj_of[ref]['right']
        final_left = self.get_final_reference(left_ref)
        return f"{final_left}[{right_ref}]"

    @staticmethod
    def match_assert(exp: str) -> Tuple[bool, str, str, str]:
        a, b, c = '', '', ''
        assert_function_pattern = r"(?:\w+\s+)?assert\((.*)\)(?:\w+\s+)?"
        match = re.match(assert_function_pattern, exp)
        if not match:
            return False, a, b, c
        content = match.group(1)
        pattern = r"(?:\w+\s+)?([\w\[\]\(\)]+)\s*==\s*([\w\[\]\(\)]+)\s*\+\s*([\w\[\]\(\)]+)(?:\w+\s+)?"
        match = re.match(pattern, content)
        if match:
            a, b, c = match.groups()
            return True, a, b, c
        pattern = r"(?:\w+\s+)?([\w\[\]\(\)]+)\s*\+\s*([\w\[\]\(\)]+)\s*==\s*([\w\[\]\(\)]+)(?:\w+\s+)?"
        match = re.match(pattern, content)
        if match:
            b, c, a = match.groups()
            return True, a, b, c
        return False, a, b, c

    @staticmethod
    def match_assignment(exp: str) -> Tuple[bool, str, str, str]:
        a, b, c = '', '', ''
        pattern = r"(?:\w+\s+)?([\w\[\]\(\)]+)\s*=\s*([\w\[\]\(\)]+)\s*\+\s*([\w\[\]\(\)]+)(?:\w+\s+)?"
        match = re.match(pattern, exp)
        if match:
            a, b, c = match.groups()
            return True, a, b, c
        return False, a, b, c

    def valid_assert(self, exp: str, a: str, b: str, c: str) -> bool:
        match, a_, b_, c_ = self.match_assert(exp)
        if not match:
            return False
        return a_ == a and (b_ == b and c_ == c or b_ == c and c_ == b)

    def valid_assignment(self, exp: str, a: str, b: str, c: str) -> bool:
        match, a_, b_, c_ = self.match_assignment(exp)
        if not match:
            return False
        return a_ == a and ((b_ == b and c_ == c) or (b_ == c and c_ == b))

    @staticmethod
    def construct_cfg(function: "FunctionContract") -> Tuple[dict[int, set], int]:
        nodes = {node.node_id for node in function.nodes}
        graph = {node: set() for node in nodes}
        for src_node in function.nodes:
            for dest_node in src_node.sons:
                graph[src_node.node_id].add(dest_node.node_id)
        return graph, function.entry_point.node_id

    @staticmethod
    def construct_reversed_cfg(function: "FunctionContract") -> Tuple[dict[int, set], int]:
        nodes = {node.node_id for node in function.nodes}
        graph = {node: set() for node in nodes}
        for src_node in function.nodes:
            for dest_node in src_node.sons:
                graph[dest_node.node_id].add(src_node.node_id)
        in_degree = {node: 0 for node in nodes}
        entries = []
        for node in graph:
            for son in graph[node]:
                in_degree[son] += 1
        for node in graph:
            if in_degree[node] == 0:
                entries.append(node)
        assert len(entries) != 0
        if len(entries) > 1:
            entry_point = -1
            nodes.add(entry_point)
            graph[entry_point] = {entry_node for entry_node in entries}
        else:
            entry_point = entries[0]
        return graph, entry_point

    @staticmethod
    def get_postorder_from_cfg(cfg: dict[int, set[int]], entry_point: int) -> List[int]:
        nodes = {node for node in cfg}
        postorder = []
        visited = set()
        stack = []
        visited.add(entry_point)
        stack.append(entry_point)
        while len(stack) != 0:
            cur_node = stack.pop()
            postorder.append(cur_node)
            for son in cfg[cur_node]:
                if son not in visited:
                    visited.add(son)
                    stack.append(son)
        return postorder[::-1]

    def calculate_dominators(self, function: "FunctionContract") -> dict[int, set[int]]:
        cfg, entry_point = self.construct_cfg(function)
        postorder = self.get_postorder_from_cfg(cfg, entry_point)
        dominators = {node: set(cfg.keys()) for node in cfg}
        dominators[entry_point] = {entry_point}
        changed = True
        while changed:
            changed = False
            for node in cfg:
                new_dominators = set()
                first = True
                for pred in postorder:
                    if node in cfg[pred]:
                        if first:
                            new_dominators = dominators[pred].copy()
                            first = False
                        else:
                            new_dominators &= dominators[pred].copy()
                new_dominators.add(node)
                if new_dominators != dominators[node]:
                    dominators[node] = new_dominators
                    changed = True
        return dominators

    def calculate_post_dominators(self, function: "FunctionContract") -> dict[int, set[int]]:
        cfg, entry_point = self.construct_reversed_cfg(function)
        postorder = self.get_postorder_from_cfg(cfg, entry_point)
        dominators = {node: set(cfg.keys()) for node in cfg}
        dominators[entry_point] = {entry_point}
        changed = True
        while changed:
            changed = False
            for node in cfg:
                new_dominators = set()
                first = True
                for pred in postorder:
                    if node in cfg[pred]:
                        if first:
                            new_dominators = dominators[pred].copy()
                            first = False
                        else:
                            new_dominators &= dominators[pred].copy()
                new_dominators.add(node)
                if new_dominators != dominators[node]:
                    dominators[node] = new_dominators
                    changed = True
        return dominators

    @staticmethod
    def get_int_bits(type_str: str) -> int:

        if type_str in {"int", "uint"}:
            return 256
        match = re.search(r'\d+', type_str)
        if match:
            return int(match.group())
        else:
            return 256

