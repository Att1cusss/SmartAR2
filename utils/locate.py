import time
from typing import Optional, List

from slither import Slither
from slither.core.cfg.node import Node, NodeType
from slither.core.declarations import FunctionContract, Contract
from slither.slithir.operations import Operation, Binary, Index

from utils.compile import change_solc_version_to, build_slither, build_ast, compile_contract, read_source_code
from utils.entity.RepairTarget import RepairTarget


def locate_slither_node_of_target_line(slither: Slither, line: int) -> Optional["Node"]:
    for contract in slither.contracts:
        for function in contract.functions:
            for node in function.nodes:
                if node.type is NodeType.ENTRYPOINT:
                    continue
                scope_of_node = node.source_mapping.lines
                if len(scope_of_node) != 1:
                    continue
                if line in scope_of_node:
                    return node
    return None


def locate_arithmetic_operations_of_target_line(slither: Slither, line: int):
    node = locate_slither_node_of_target_line(slither, line)
    print(node.type)
    for son in node.sons:
        print(son.type)
        print(son.expression)
        for grandson in son.sons:
            print(grandson.type)
            print(grandson.expression)


def locate_function_node_of_target_line(slither: Slither, line: int) -> Optional[FunctionContract]:
    for contract in slither.contracts:
        for function in contract.functions:
            if line in function.source_mapping.lines:
                return function
    return None


def locate_slither_node_of_target_function(slither: Slither, contractName: str, functionName: str) -> Optional[FunctionContract]:
    contract = next((c for c in slither.contracts if c.name == contractName and
                     (str(c.contract_kind) == 'contract' or str(c.contract_kind) == 'library')
                     ), None)
    if contract is None:
        print(f'Contract {contractName} not found.')
        return None
    function = next((f for f in contract.functions if f.name == functionName and len(f.nodes) != 0), None)
    if function is None:
        print(f'Function {functionName} not found in contract {contractName}.')
        return
    return function


# locate and return [arithmetic operation AST nodes to be repaired] according to line number
def locate_arithmetic_operations_ast_nodes_by_line_number(source_node, source_code, line_number) -> Optional[List]:
    if source_node is None or source_code is None or source_code == '' or line_number is None:
        return None
    # locate to contract and function node
    contract_node = None
    function_node = None
    for contract in source_node:
        if contract.nodeType == 'ContractDefinition':
            for function in contract:
                if function.nodeType == 'FunctionDefinition':
                    function_scope = function.get_line_numbers(source_code)
                    if function_scope[0] <= line_number <= function_scope[1]:
                        contract_node = contract
                        function_node = function
    if contract_node is None or function_node is None:
        return None
    # locate to statement node
    statement_node = None
    for node in function_node:
        scope = node.get_line_numbers(source_code)
        if scope[0] <= line_number <= scope[1]:
            statement_node = node
            break
    if statement_node is None:
        return None
    # locate to all arithmetic operation in statement node (binary op & unary op & assignment)
    binary_operations = []
    unary_operations = []
    assignments = []
    located_nodes = []
    repair_targets = ['+', '-', '*', '/', '+=', '-=', '*=', '/=', '++', '--']
    binary_operations += statement_node.children(
        depth=100,
        filters={'nodeType': "BinaryOperation"},
        include_children=True
    )
    unary_operations += statement_node.children(
        depth=100,
        filters={'nodeType': "UnaryOperation"},
        include_children=True
    )
    assignments += statement_node.children(
        depth=100,
        filters={'nodeType': "Assignment"},
        include_children=True
    )
    if len(binary_operations) == 0 and len(unary_operations) == 0 and len(assignments) == 0:
        return None
    # sometimes statement has more than one line, may contain redundant op, need filter
    for assignment in assignments:
        code = assignment.extract_code(source_code, True)
        if int(code.split(": ")[0]) == line_number and assignment.operator in repair_targets:
            located_nodes.append(assignment)
    for binary_operation in binary_operations:
        code = binary_operation.extract_code(source_code, True)
        if int(code.split(": ")[0]) == line_number and binary_operation.operator in repair_targets:
            located_nodes.append(binary_operation)
    for unary_operation in unary_operations:
        code = unary_operation.extract_code(source_code, True)
        if int(code.split(": ")[0]) == line_number and unary_operation.operator in repair_targets:
            located_nodes.append(unary_operation)

    return sorted(located_nodes, key=lambda _node: len(_node.extract_code(source_code, False)))


def locate_repair_targets(source_node, slither: Slither, source_code, line_number) -> List[RepairTarget]:
    # print('[Locating Repair Targets]')
    start_time = time.time()
    repair_targets = []
    ast_targets = locate_arithmetic_operations_ast_nodes_by_line_number(source_code=source_code,
                                                                        source_node=source_node,
                                                                        line_number=line_number)
    if ast_targets is None or len(ast_targets) == 0:
        return repair_targets
    unmatched_repair_targets = {target for target in ast_targets}
    unmatched_repair_targets_list = [target for target in ast_targets]
    unmatched_binary_ssa = set()
    unmatched_binary_ssa_list = []
    slither_node = locate_slither_node_of_target_line(slither=slither, line=line_number)
    slither_function_node = locate_function_node_of_target_line(slither=slither, line=line_number)
    ir_variable_of_target = {}
    ir_variable_of_target_code = {}
    ir_of_target = {}
    reference_of_ir_variable = {}
    if slither_node is not None:
        slither_node: "Node"
        for ir in slither_node.irs_ssa:
            if isinstance(ir, Index):
                reference_of_ir_variable[
                    ir.lvalue.name] = ir.variable_left.name + '[' + ir.variable_right.name + ']'
            elif isinstance(ir, Binary):
                unmatched_binary_ssa.add(ir)
                unmatched_binary_ssa_list.append(ir)
    binary_operator_of_unary_operator = {'++': '+', '--': '-'}
    binary_operator_of_assignment_operator = {'+=': '+', '-=': '-', '*=': '*', '/=': '/'}
    for target in ast_targets:
        node_type = target.nodeType
        if node_type == 'BinaryOperation':
            if slither_node is not None:
                slither_node: "Node"
                for ir in unmatched_binary_ssa:
                    if isinstance(ir, Binary) and ir.type_str == target.operator:
                        ast_left_expression = target.leftExpression.extract_code(source_code, False)
                        ast_right_expression = target.rightExpression.extract_code(source_code, False)
                        ir_variable_left_name = ir.variable_left.name
                        ir_variable_right_name = ir.variable_right.name
                        ir_lvalue_name = ir.lvalue.name
                        if ast_left_expression.startswith('(') and ast_left_expression.endswith(')'):
                            ast_left_expression = ast_left_expression[1:-1]
                        if ast_right_expression.startswith('(') and ast_right_expression.endswith(')'):
                            ast_right_expression = ast_right_expression[1:-1]
                        if ast_left_expression in ir_variable_of_target_code:
                            ast_left_expression = ir_variable_of_target_code[ast_left_expression].name
                        if ast_right_expression in ir_variable_of_target_code:
                            ast_right_expression = ir_variable_of_target_code[ast_right_expression].name
                        if ir_variable_left_name in reference_of_ir_variable:
                            ir_variable_left_name = reference_of_ir_variable[ir_variable_left_name]
                        if ir_variable_right_name in reference_of_ir_variable:
                            ir_variable_right_name = reference_of_ir_variable[ir_variable_right_name]
                        if ir_lvalue_name in reference_of_ir_variable:
                            ir_lvalue_name = reference_of_ir_variable[ir_lvalue_name]
                        if ir_variable_left_name == ast_left_expression and ir_variable_right_name == ast_right_expression:
                            ir_variable_of_target[target] = ir.lvalue
                            ir_variable_of_target_code[target.extract_code(source_code, False)] = ir.lvalue
                            ir_of_target[target] = ir
                            repair_targets.append(RepairTarget(
                                source_code=source_code,
                                slither=slither,
                                slither_function_node=slither_function_node,
                                slither_statement_node=slither_node,
                                ast_root=source_node,
                                ast_node=target,
                                ir=ir
                            ))
                            unmatched_repair_targets.remove(target)
                            unmatched_binary_ssa.remove(ir)
                            break
                        if (ir_variable_left_name == ast_left_expression) or \
                                (ir_variable_right_name == ast_right_expression):
                            ir_variable_of_target[target] = ir.lvalue
                            ir_variable_of_target_code[target.extract_code(source_code, False)] = ir.lvalue
                            ir_of_target[target] = ir
                            repair_targets.append(RepairTarget(
                                source_code=source_code,
                                slither=slither,
                                slither_function_node=slither_function_node,
                                slither_statement_node=slither_node,
                                ast_root=source_node,
                                ast_node=target,
                                ir=ir
                            ))
                            unmatched_repair_targets.remove(target)
                            unmatched_binary_ssa.remove(ir)
                            break
        elif node_type == 'UnaryOperation':
            for ir in slither_node.irs_ssa:
                if isinstance(ir, Binary) and ir.type_str == binary_operator_of_unary_operator[target.operator]:
                    ast_sub_expression = target.subExpression.extract_code(source_code, False)
                    ir_variable_left_name = ir.variable_left.name
                    ir_variable_right_name = ir.variable_right.name
                    ir_lvalue_name = ir.lvalue.name
                    if ast_sub_expression.startswith('(') and ast_sub_expression.endswith(')'):
                        ast_sub_expression = ast_sub_expression[1:-1]
                    if ast_sub_expression in ir_variable_of_target_code:
                        ast_sub_expression = ir_variable_of_target_code[ast_sub_expression].name
                    if ir_variable_left_name in reference_of_ir_variable:
                        ir_variable_left_name = reference_of_ir_variable[ir_variable_left_name]
                    if ir_variable_right_name in reference_of_ir_variable:
                        ir_variable_right_name = reference_of_ir_variable[ir_variable_right_name]
                    if ir_lvalue_name in reference_of_ir_variable:
                        ir_lvalue_name = reference_of_ir_variable[ir_lvalue_name]
                    if ir_variable_left_name == ast_sub_expression and str(ir.variable_right) == '1' and \
                            ir_lvalue_name == ir_variable_left_name:
                        ir_variable_of_target[target] = ir.lvalue
                        ir_variable_of_target_code[target.extract_code(source_code, False)] = ir.lvalue
                        ir_of_target[target] = ir
                        repair_targets.append(RepairTarget(
                            source_code=source_code,
                            slither=slither,
                            slither_function_node=slither_function_node,
                            slither_statement_node=slither_node,
                            ast_root=source_node,
                            ast_node=target,
                            ir=ir
                        ))
                        unmatched_repair_targets.remove(target)
                        unmatched_binary_ssa.remove(ir)
                        break
        elif node_type == 'Assignment':
            for ir in slither_node.irs_ssa:
                if isinstance(ir, Binary) and ir.type_str == binary_operator_of_assignment_operator[target.operator] \
                        and (ir.lvalue.name == ir.variable_left.name or ir.lvalue.name == ir.variable_right.name):
                    ast_left_expression = target.leftHandSide.extract_code(source_code, False)
                    ast_right_expression = target.rightHandSide.extract_code(source_code, False)
                    ir_variable_left_name = ir.variable_left.name
                    ir_variable_right_name = ir.variable_right.name
                    ir_lvalue_name = ir.lvalue.name
                    if ast_left_expression.startswith('(') and ast_left_expression.endswith(')'):
                        ast_left_expression = ast_left_expression[1:-1]
                    if ast_right_expression.startswith('(') and ast_right_expression.endswith(')'):
                        ast_right_expression = ast_right_expression[1:-1]
                    if ast_left_expression in ir_variable_of_target_code:
                        ast_left_expression = ir_variable_of_target_code[ast_left_expression].name
                    if ast_right_expression in ir_variable_of_target_code:
                        ast_right_expression = ir_variable_of_target_code[ast_right_expression].name
                    if ir_variable_left_name in reference_of_ir_variable:
                        ir_variable_left_name = reference_of_ir_variable[ir_variable_left_name]
                    if ir_variable_right_name in reference_of_ir_variable:
                        ir_variable_right_name = reference_of_ir_variable[ir_variable_right_name]
                    if ir_lvalue_name in reference_of_ir_variable:
                        ir_lvalue_name = reference_of_ir_variable[ir_lvalue_name]
                    if ir_lvalue_name == ast_left_expression and (
                            (ir_variable_left_name == ast_left_expression and
                             ir_variable_right_name == ast_right_expression) or
                            (ir_variable_left_name == ast_right_expression and
                             ir_variable_right_name == ast_left_expression)
                    ):
                        ir_variable_of_target[target] = ir.lvalue
                        ir_variable_of_target_code[target.extract_code(source_code, False)] = ir.lvalue
                        ir_of_target[target] = ir
                        repair_targets.append(RepairTarget(
                            source_code=source_code,
                            slither=slither,
                            slither_function_node=slither_function_node,
                            slither_statement_node=slither_node,
                            ast_root=source_node,
                            ast_node=target,
                            ir=ir
                        ))
                        unmatched_repair_targets.remove(target)
                        unmatched_binary_ssa.remove(ir)
                        break
    if len(unmatched_repair_targets) == 1 and len(unmatched_binary_ssa) == 1:
        target = unmatched_repair_targets.pop()
        ir = unmatched_binary_ssa.pop()
        ir_variable_of_target[target] = ir.lvalue
        ir_variable_of_target_code[target.extract_code(source_code, False)] = ir.lvalue
        ir_of_target[target] = ir
        repair_targets.append(RepairTarget(
            source_code=source_code,
            slither=slither,
            slither_function_node=slither_function_node,
            slither_statement_node=slither_node,
            ast_root=source_node,
            ast_node=target,
            ir=ir
        ))
    targets_need_remove = set()
    for target in unmatched_repair_targets:
        if target.nodeType == 'UnaryOperation' and len(slither_node.sons) == 1 and slither_node.sons[0].type == NodeType.STARTLOOP:
            begin_loop_node = slither_node.sons[0]
            for son in begin_loop_node.sons:
                if son.type == NodeType.IFLOOP:
                    for father in son.fathers:
                        if str(target.operator) in str(father.expression) and \
                                target.subExpression.extract_code(source_code, False) in str(father.expression):
                            binary_ir_cnt = 0
                            for ir in father.irs_ssa:
                                if isinstance(ir, Binary):
                                    binary_ir = ir
                                    binary_ir_cnt += 1
                            if binary_ir_cnt == 1:
                                ir_variable_of_target[target] = binary_ir.lvalue
                                ir_variable_of_target_code[target.extract_code(source_code, False)] = binary_ir.lvalue
                                ir_of_target[target] = binary_ir
                                repair_targets.append(RepairTarget(
                                    source_code=source_code,
                                    slither=slither,
                                    slither_function_node=slither_function_node,
                                    slither_statement_node=father,
                                    ast_root=source_node,
                                    ast_node=target,
                                    ir=binary_ir
                                ))
                                targets_need_remove.add(target)
    for target in targets_need_remove:
        unmatched_repair_targets.remove(target)
    if len(unmatched_repair_targets_list) == len(unmatched_binary_ssa):
        for i in range(len(unmatched_repair_targets_list)):
            target = unmatched_repair_targets_list[i]
            ir = unmatched_binary_ssa_list[i]
            if target not in unmatched_repair_targets:
                continue
            ir_variable_of_target[target] = ir.lvalue
            ir_variable_of_target_code[target.extract_code(source_code, False)] = ir.lvalue
            ir_of_target[target] = ir
            repair_targets.append(RepairTarget(
                source_code=source_code,
                slither=slither,
                slither_function_node=slither_function_node,
                slither_statement_node=slither_node,
                ast_root=source_node,
                ast_node=target,
                ir=ir
            ))

    end_time = time.time()
    elapsed_time = end_time - start_time
    return repair_targets


def locate_contract_by_name(slither: Slither, contract_name: str) -> Optional[Contract]:
    for contract in slither.contracts:
        if contract.name == contract_name:
            return contract
    return None
