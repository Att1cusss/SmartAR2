from collections import defaultdict, deque
from typing import List, Dict, Tuple, Set, DefaultDict, Union

from graphviz import Digraph
from slither import Slither
from slither.core.cfg.node import Node
from slither.core.declarations import FunctionContract, Function
from slither.core.declarations.solidity_variables import SOLIDITY_FUNCTIONS
from slither.core.solidity_types.elementary_type import ElementaryTypeName, Uint, Int, Min_Uint, Max_Uint, Min_Int, \
    Max_Int
from slither.slithir.operations import *
from slither.slithir.operations.codesize import CodeSize
from slither.slithir.variables import ReferenceVariable
from z3 import Solver, And, Bool, BitVec, UGE, ULE, Or, UGT, ULT, sat, Not, unsat, BoolRef, ArithRef

from utils.compile import build_slither, change_solc_version_to, read_source_code, build_ast, compile_contract
from utils.entity.ContractPath import ContractPath
from utils.entity.Invariant import Invariant
from utils.entity.RepairTarget import RepairTarget
from utils.locate import locate_repair_targets


class RedundantTargetReducer:
    def __init__(self, slither: Slither, repair_targets: List[RepairTarget], can_overflow=False):
        self.debug = False
        self.LOOP_LIMIT = 1
        self.slither = slither
        self.context_id = 0
        self.z3v_of = {}
        self.type_constrains_of = {}
        self.can_overflow = can_overflow
        self.random_number_index = 0

        self.repair_targets = repair_targets

        self.uncheck_z3v_name = set()

    def enumerate_contract_path(self, current_node: Node, current_ir_idx: int,
                                current_path: ContractPath, paths: [ContractPath],
                                node_visit_counter: Dict["Node", int], context: int):
        while current_ir_idx < len(current_node.irs_ssa):
            ir = current_node.irs_ssa[current_ir_idx]
            current_ir_idx += 1
            current_path.append_ir(ir, context)
            if isinstance(ir, Call):
                if (isinstance(ir, LibraryCall) or isinstance(ir, InternalCall)) and \
                        (ir.function.entry_point is not None and ir.function.entry_point.irs_ssa is not None):
                    sub_paths = []
                    self.context_id += 1
                    self.enumerate_contract_path(
                        current_node=ir.function.entry_point,
                        current_ir_idx=0,
                        current_path=ContractPath(),
                        paths=sub_paths,
                        node_visit_counter={},
                        context=self.context_id
                    )
                    for sub_path in sub_paths:
                        sub_path: ContractPath
                        if sub_path.is_finished():
                            continue
                        copy_current_path = current_path.deepcopy()
                        copy_current_path.append_path(sub_path)
                        self.enumerate_contract_path(
                            current_node=current_node,
                            current_ir_idx=current_ir_idx,
                            current_path=copy_current_path,
                            paths=paths,
                            node_visit_counter=node_visit_counter,
                            context=context
                        )
                    return

        if len(current_node.sons) == 0 and not current_path.is_finished():
            paths.append(current_path.deepcopy())
            return
        for next_node in current_node.sons:
            if node_visit_counter.get(next_node, 0) >= self.LOOP_LIMIT:
                continue
            node_visit_counter_copy = node_visit_counter.copy()
            node_visit_counter_copy[next_node] = node_visit_counter.get(next_node, 0) + 1
            self.enumerate_contract_path(next_node, 0, current_path.deepcopy(), paths, node_visit_counter_copy, context)

    def parse_contract_path(self, path: ContractPath):
        reference_of = {}
        ir_types_stat = {}

        while not path.is_finished():

            if path.is_revert():
                break

            ir = path.get_next_ir()

            ir_types_stat[str(type(ir))] = ir_types_stat.get(str(type(ir)), 0) + 1
            constrain_idx_begin = len(path.constrains)

            if isinstance(ir, Assignment):
                ir: Assignment

                prev_lv_z3_name = None
                if str(ir.lvalue) in reference_of:
                    left = reference_of[str(ir.lvalue)]['left']
                    right = reference_of[str(ir.lvalue)]['right']
                    lv = f'{left}{right}'
                    prev_lv_z3_name = f'{path.get_context()}#{lv}'
                    if isinstance(ir.lvalue, ReferenceVariable) and str(ir.lvalue.points_to_origin) != left:
                        lv = lv.replace(left, str(ir.lvalue.points_to_origin))
                else:
                    lv = str(ir.lvalue)

                if str(ir.rvalue) in reference_of:
                    left = reference_of[str(ir.rvalue)]['left']
                    right = reference_of[str(ir.rvalue)]['right']
                    rv = f'{left}{right}'
                else:
                    rv = str(ir.rvalue)

                lv_z3_name = f'{path.get_context()}#{lv}'
                rv_z3_name = f'{path.get_context()}#{rv}'

                path.add_path_constrain(self.register_z3v(v_name=lv_z3_name, v_type=str(ir.lvalue.type)))
                path.add_path_constrain(self.register_z3v(v_name=rv_z3_name, v_type=str(ir.rvalue.type)))

                path.add_path_constrain(self.z3v_of[lv_z3_name] == self.z3v_of[rv_z3_name])

                if str(ir.rvalue) in reference_of:
                    none_context_name = rv_z3_name.split('#')[1]
                    point_to_name = none_context_name.split('[')[0].rsplit('_', 1)[0]
                    index_name = '[' + none_context_name.split('[', 1)[1]
                    path.register_alias(point_to_name + index_name, none_context_name)
                else:
                    path.register_alias(ir.rvalue.name, str(ir.rvalue))
                if str(ir.lvalue) in reference_of:
                    none_context_name = lv_z3_name.split('#')[1]
                    point_to_name = none_context_name.split('[')[0].rsplit('_', 1)[0]
                    index_name = '[' + none_context_name.split('[', 1)[1]
                    path.register_alias(point_to_name + index_name, none_context_name)
                else:
                    path.register_alias(ir.lvalue.name, str(ir.lvalue))

                if isinstance(ir.lvalue, ReferenceVariable) and str(ir.lvalue.points_to_origin) == reference_of[str(ir.lvalue)]['left']:
                    assert True == False

                if isinstance(ir.lvalue, ReferenceVariable) and str(ir.lvalue.points_to_origin) != \
                        reference_of[str(ir.lvalue)]['left']:
                    if prev_lv_z3_name is not None and prev_lv_z3_name in self.z3v_of:
                        collection_name = str(ir.lvalue.points_to_origin).rsplit('_', 1)[0]
                        prev_lv_z3v = self.z3v_of[prev_lv_z3_name]
                        rv_z3v = self.z3v_of[rv_z3_name]
                        if collection_name not in path.delta_of_collection:
                            path.delta_of_collection[collection_name] = []
                        path.delta_of_collection[collection_name].append(rv_z3v - prev_lv_z3v)
                    reference_of[str(ir.lvalue)]['left'] = str(ir.lvalue.points_to_origin)

            elif isinstance(ir, Binary):
                ir: Binary

                prev_lv_z3_name = None
                if str(ir.lvalue) in reference_of:
                    left = reference_of[str(ir.lvalue)]['left']
                    right = reference_of[str(ir.lvalue)]['right']
                    lv = f'{left}{right}'
                    if isinstance(ir.lvalue, ReferenceVariable) and str(ir.lvalue.points_to_origin) != left:
                        prev_lv_z3_name = f'{path.get_context()}#{lv}'
                        lv = lv.replace(left, str(ir.lvalue.points_to_origin))
                else:
                    lv = str(ir.lvalue)
                if str(ir.variable_left) in reference_of:
                    left = reference_of[str(ir.variable_left)]['left']
                    right = reference_of[str(ir.variable_left)]['right']
                    vl = f'{left}{right}'
                else:
                    vl = str(ir.variable_left)
                if str(ir.variable_right) in reference_of:
                    left = reference_of[str(ir.variable_right)]['left']
                    right = reference_of[str(ir.variable_right)]['right']
                    vr = f'{left}{right}'
                else:
                    vr = str(ir.variable_right)
                lv_z3_name = f'{path.get_context()}#{lv}'
                vl_z3_name = f'{path.get_context()}#{vl}'
                vr_z3_name = f'{path.get_context()}#{vr}'
                path.add_path_constrain(self.register_z3v(v_name=lv_z3_name, v_type=str(ir.lvalue.type)))
                path.add_path_constrain(self.register_z3v(v_name=vl_z3_name, v_type=str(ir.variable_left.type)))
                path.add_path_constrain(self.register_z3v(v_name=vr_z3_name, v_type=str(ir.variable_right.type)))
                a = self.z3v_of[vl_z3_name]
                b = self.z3v_of[vr_z3_name]
                if ir.type_str == '||':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == Or(a, b))
                elif ir.type_str == '&&':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == And(a, b))
                elif ir.type_str == '>':
                    if str(ir.variable_left.type) in Uint:
                        path.add_path_constrain(self.z3v_of[lv_z3_name] == UGT(a, b))
                    else:
                        path.add_path_constrain(self.z3v_of[lv_z3_name] == (a > b))
                elif ir.type_str == '>=':
                    if str(ir.variable_left.type) in Uint:
                        path.add_path_constrain(self.z3v_of[lv_z3_name] == UGE(a, b))
                    else:
                        path.add_path_constrain(self.z3v_of[lv_z3_name] == (a >= b))
                elif ir.type_str == '<':
                    if str(ir.variable_left.type) in Uint:
                        path.add_path_constrain(self.z3v_of[lv_z3_name] == ULT(a, b))
                    else:
                        path.add_path_constrain(self.z3v_of[lv_z3_name] == (a < b))
                elif ir.type_str == '<=':
                    if str(ir.variable_left.type) in Uint:
                        path.add_path_constrain(self.z3v_of[lv_z3_name] == ULE(a, b))
                    else:
                        path.add_path_constrain(self.z3v_of[lv_z3_name] == (a <= b))
                elif ir.type_str == '==':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == (a == b))
                elif ir.type_str == '!=':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == (a != b))
                elif ir.type_str == '+':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == (a + b))
                    if not self.can_overflow:
                        if str(ir.variable_left.type) in Uint:
                            not_overflow_condition = UGE(a + b, a)
                            path.add_path_constrain(not_overflow_condition)
                        elif str(ir.variable_left.type) in Int:
                            not_overflow_condition = Or([
                                And([a > 0, b > 0, a + b > a]), And([a < 0, b < 0, a + b < a])
                            ])
                            path.add_path_constrain(not_overflow_condition)
                elif ir.type_str == '-':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == (a - b))
                    if not self.can_overflow:
                        if str(ir.variable_left.type) in Uint:
                            not_overflow_condition = UGE(a, b)
                            path.add_path_constrain(not_overflow_condition)
                        elif str(ir.variable_left.type) in Int:
                            not_overflow_condition = Or([
                                And([a > 0, b < 0, a - b > a]), And([a < 0, b > 0, a - b < a])
                            ])
                            path.add_path_constrain(not_overflow_condition)
                elif ir.type_str == '*':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == (a * b))
                    if not self.can_overflow:
                        not_overflow_condition = Or([a == 0, And([a != 0, a * b / a == b])])
                        path.add_path_constrain(not_overflow_condition)
                elif ir.type_str == '/':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == (a / b))
                elif ir.type_str == '%':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == (a % b))
                elif ir.type_str == '**':
                    pass

                if str(ir.variable_left) in reference_of:
                    none_context_name = vl_z3_name.split('#')[1]  # 0#xxx_1[xxx] => xxx_1[xxx]
                    point_to_name = none_context_name.split('[')[0].rsplit('_', 1)[0]  # xxx_1[xxx] => xxx
                    index_name = '[' + none_context_name.split('[', 1)[1]  # xxx_1[xxx] => [xxx]
                    path.register_alias(point_to_name + index_name, none_context_name)  # xxx[xxx] <==> xxx_1[xxx]
                else:
                    path.register_alias(ir.variable_left.name, str(ir.variable_left))
                if str(ir.variable_right) in reference_of:
                    none_context_name = vr_z3_name.split('#')[1]  # 0#xxx_1[xxx] => xxx_1[xxx]
                    point_to_name = none_context_name.split('[')[0].rsplit('_', 1)[0]  # xxx_1[xxx] => xxx
                    index_name = '[' + none_context_name.split('[', 1)[1]  # xxx_1[xxx] => [xxx]
                    path.register_alias(point_to_name + index_name, none_context_name)  # xxx[xxx] <==> xxx_1[xxx]
                else:
                    path.register_alias(ir.variable_right.name, str(ir.variable_right))
                if str(ir.lvalue) in reference_of:
                    none_context_name = lv_z3_name.split('#')[1]  # 0#xxx_1[xxx] => xxx_1[xxx]
                    point_to_name = none_context_name.split('[')[0].rsplit('_', 1)[0]  # xxx_1[xxx] => xxx
                    index_name = '[' + none_context_name.split('[', 1)[1]  # xxx_1[xxx] => [xxx]
                    path.register_alias(point_to_name + index_name, none_context_name)  # xxx[xxx] <==> xxx_1[xxx]
                else:
                    path.register_alias(ir.lvalue.name, str(ir.lvalue))

                if isinstance(ir.lvalue, ReferenceVariable) and str(ir.lvalue.points_to_origin) != \
                        reference_of[str(ir.lvalue)]['left']:
                    if prev_lv_z3_name is not None and prev_lv_z3_name in self.z3v_of:
                        collection_name = str(ir.lvalue.points_to_origin).rsplit('_', 1)[0]
                        prev_lv_z3v = self.z3v_of[prev_lv_z3_name]
                        if collection_name not in path.delta_of_collection:
                            path.delta_of_collection[collection_name] = []
                        if ir.type_str == '+':
                            path.delta_of_collection[collection_name].append(b)
                        elif ir.type_str == '-':
                            path.delta_of_collection[collection_name].append(-1 * b)
                        else:
                            path.delta_of_collection[collection_name].append(self.register_random_z3v())
                    reference_of[str(ir.lvalue)]['left'] = str(ir.lvalue.points_to_origin)

            elif isinstance(ir, Call):
                ir: Call

                if isinstance(ir, LibraryCall) or isinstance(ir, InternalCall):

                    if isinstance(ir, LibraryCall):
                        ir: LibraryCall

                    if isinstance(ir, InternalCall):
                        ir: InternalCall

                    alias_of_parameter = {}
                    for parameter in ir.function.parameters:
                        alias_of_parameter[parameter.name] = self.get_first_alias(ir.function, parameter.name)
                    assert len(ir.arguments) == len(ir.function.parameters)
                    for i in range(len(ir.arguments)):
                        argument_variable = ir.arguments[i]
                        if str(argument_variable) in reference_of:
                            left = reference_of[str(argument_variable)]['left']
                            right = reference_of[str(argument_variable)]['right']
                            argument_variable_name = f'{left}{right}'
                            if isinstance(argument_variable, ReferenceVariable) and str(
                                    argument_variable.points_to_origin) != left:
                                argument_variable_name = argument_variable_name.replace(left,
                                                                                        str(argument_variable.points_to_origin))
                        else:
                            argument_variable_name = str(argument_variable)
                        argument_variable_z3_name = f'{path.get_context()}#{argument_variable_name}'
                        path.add_path_constrain(
                            self.register_z3v(
                                v_name=argument_variable_z3_name, v_type=str(argument_variable.type)
                            )
                        )
                        parameter_variable = ir.function.parameters[i]
                        parameter_variable_z3_name = f'{path.get_next_context()}#{alias_of_parameter[parameter_variable.name]}'
                        path.add_path_constrain(
                            self.register_z3v(
                                v_name=parameter_variable_z3_name, v_type=str(parameter_variable.type)
                            )
                        )
                        path.add_path_constrain(
                            self.z3v_of[argument_variable_z3_name] == self.z3v_of[parameter_variable_z3_name]
                        )
                        if str(argument_variable) in reference_of:
                            none_context_name = argument_variable_z3_name.split('#')[1]
                            point_to_name = none_context_name.split('[')[0].rsplit('_', 1)[0]
                            index_name = '[' + none_context_name.split('[', 1)[1]
                            path.register_alias(point_to_name + index_name,
                                                none_context_name)
                        else:
                            path.register_alias(argument_variable.name, str(argument_variable))
                        try:
                            if isinstance(argument_variable, ReferenceVariable) and str(
                                    argument_variable.points_to_origin) != reference_of[str(argument_variable)]['left']:
                                reference_of[str(argument_variable)]['left'] = str(argument_variable.points_to_origin)
                        except Exception as e:
                            pass

                    if ir.lvalue is not None and str(ir.lvalue.type) in ElementaryTypeName:
                        if str(ir.lvalue) in reference_of:
                            left = reference_of[str(ir.lvalue)]['left']
                            right = reference_of[str(ir.lvalue)]['right']
                            lv = f'{left}{right}'
                            if isinstance(ir.lvalue, ReferenceVariable) and str(ir.lvalue.points_to_origin) != left:
                                lv = lv.replace(left, str(ir.lvalue.points_to_origin))
                        else:
                            lv = str(ir.lvalue)
                        lv_z3_name = f'{path.get_context()}#{lv}'
                        path.add_path_constrain(self.register_z3v(v_name=lv_z3_name, v_type=str(ir.lvalue.type)))
                        path.register_return_value_receiver(lv_z3_name)
                        if isinstance(ir.lvalue, ReferenceVariable) and str(ir.lvalue.points_to_origin) != \
                                reference_of[str(ir.lvalue)]['left']:
                            reference_of[str(ir.lvalue)]['left'] = str(ir.lvalue.points_to_origin)

                elif isinstance(ir, SolidityCall):
                    ir: SolidityCall

                    assert ir.function.name in SOLIDITY_FUNCTIONS
                    if ir.function.name == 'assert(bool)' or ir.function.name == "require(bool)" \
                            or ir.function.name == "require(bool,string)":
                        argument_variable = None
                        for argument in ir.arguments:
                            if str(argument.type) == 'bool':
                                argument_variable = argument
                                break
                        assert argument_variable is not None
                        if str(argument_variable) in reference_of:
                            left = reference_of[str(argument_variable)]['left']
                            right = reference_of[str(argument_variable)]['right']
                            argument_variable_name = f'{left}{right}'
                        else:
                            argument_variable_name = str(argument_variable)
                        argument_variable_z3_name = f'{path.get_context()}#{argument_variable_name}'
                        path.add_path_constrain(
                            self.register_z3v(
                                v_name=argument_variable_z3_name, v_type=str(argument_variable.type)
                            )
                        )
                        path.add_path_constrain(self.z3v_of[argument_variable_z3_name] == True)

                    elif ir.function.name == "revert()" or ir.function.name == "revert(string)" \
                            or ir.function.name == "revert ":
                        path.set_revert(True)
                    else:
                        pass

            elif isinstance(ir, CodeSize):
                ir: CodeSize

            elif isinstance(ir, Condition):
                ir: Condition
                if ir.value.name is not None and (ir.value.name == 'True' or ir.value.name == 'False'):
                    if ir.value.name == 'True' and path.get_next_node() in [path.get_current_node().son_false]:
                        path.set_revert(True)
                    elif ir.value.name == 'False' and path.get_next_node() in [path.get_current_node().son_true]:
                        path.set_revert(True)
                else:
                    if str(ir.value) in reference_of:
                        left = reference_of[str(ir.value)]['left']
                        right = reference_of[str(ir.value)]['right']
                        v_name = f'{left}{right}'
                    else:
                        v_name = str(ir.value)
                    v_name = f'{path.get_context()}#{v_name}'
                    path.add_path_constrain(
                        self.register_z3v(
                            v_name=v_name, v_type=str(ir.value.type)
                        )
                    )
                    if path.get_next_node() in [path.get_current_node().son_true]:
                        path.add_path_constrain(self.z3v_of[v_name] == True)
                    else:
                        path.add_path_constrain(self.z3v_of[v_name] == False)

            elif isinstance(ir, Delete):
                ir: Delete

            elif isinstance(ir, EventCall):
                ir: EventCall

            elif isinstance(ir, HighLevelCall):
                ir: HighLevelCall

            elif isinstance(ir, Index):
                ir: Index
                left = f'{str(ir.variable_left)}'
                right = f'[{str(ir.variable_right)}]'
                while left in reference_of:
                    right = reference_of[left]['right'] + right
                    left = reference_of[left]['left']
                reference_of[str(ir.lvalue)] = {}
                reference_of[str(ir.lvalue)]['left'] = left
                reference_of[str(ir.lvalue)]['right'] = right
                ref_z3_name = f'{path.get_context()}#{str(ir.lvalue)}'
                point_to_z3_name = f'{path.get_context()}#{left}{right}'

            elif isinstance(ir, InitArray):
                ir: InitArray

            elif isinstance(ir, InternalDynamicCall):
                ir: InternalDynamicCall

            elif isinstance(ir, LowLevelCall):
                ir: LowLevelCall

            elif isinstance(ir, Member):
                ir: Member

            elif isinstance(ir, NewArray):
                ir: NewArray

            elif isinstance(ir, NewContract):
                ir: NewContract

            elif isinstance(ir, NewElementaryType):
                ir: NewElementaryType

            elif isinstance(ir, NewStructure):
                ir: NewStructure

            elif isinstance(ir, Nop):
                ir: Nop

            elif isinstance(ir, Phi):
                ir: Phi

                if len(ir.nodes) == 0 or len(ir.rvalues) == 0:
                    continue
                if path.get_latest_alias_in_current_context(ir.lvalue.name) is None:
                    continue
                else:
                    prev_latest_alias = path.get_latest_alias_in_current_context(ir.lvalue.name)
                    phi_lv__z3_name = f'{path.get_context()}#{str(ir.lvalue)}'
                    if phi_lv__z3_name not in self.z3v_of:
                        path.add_path_constrain(
                            self.register_z3v(
                                v_name=phi_lv__z3_name, v_type=str(ir.lvalue.type)
                            )
                        )
                    path.add_path_constrain(
                        self.z3v_of[f'{path.get_context()}#{prev_latest_alias}'] == self.z3v_of[phi_lv__z3_name]
                    )
                    path.register_alias(ir.lvalue.name, str(ir.lvalue))

            elif isinstance(ir, Return):
                ir: Return
                for return_variable in reversed(ir.values):
                    if path.get_context() == 0:
                        continue
                    if str(return_variable.type) not in ElementaryTypeName:
                        path.get_return_value_receiver()
                        continue
                    if str(return_variable) in reference_of:
                        left = reference_of[str(return_variable)]['left']
                        right = reference_of[str(return_variable)]['right']
                        return_value_name = f'{left}{right}'
                    else:
                        return_value_name = str(return_variable)
                    return_value_z3_name = f'{path.get_context()}#{return_value_name}'
                    path.add_path_constrain(
                        self.register_z3v(v_name=return_value_z3_name, v_type=str(return_variable.type)))
                    path.add_path_constrain(
                        self.z3v_of[path.get_return_value_receiver()] == self.z3v_of[return_value_z3_name]
                    )

            elif isinstance(ir, Send):
                ir: Send

            elif isinstance(ir, Transfer):
                ir: Transfer

            elif isinstance(ir, TypeConversion):
                ir: TypeConversion

            elif isinstance(ir, Unary):
                ir: Unary
                if str(ir.lvalue) in reference_of:
                    left = reference_of[str(ir.lvalue)]['left']
                    right = reference_of[str(ir.lvalue)]['right']
                    lv = f'{left}{right}'
                else:
                    lv = str(ir.lvalue)
                if str(ir.rvalue) in reference_of:
                    left = reference_of[str(ir.rvalue)]['left']
                    right = reference_of[str(ir.rvalue)]['right']
                    rv = f'{left}{right}'
                else:
                    rv = str(ir.rvalue)
                lv_z3_name = f'{path.get_context()}#{lv}'
                rv_z3_name = f'{path.get_context()}#{rv}'
                path.add_path_constrain(self.register_z3v(v_name=lv_z3_name, v_type=str(ir.lvalue.type)))
                path.add_path_constrain(self.register_z3v(v_name=rv_z3_name, v_type=str(ir.rvalue.type)))
                if ir.type_str == 'UnaryType.BANG':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == Not(self.z3v_of[rv_z3_name]))
                elif ir.type_str == 'UnaryType.TILD':
                    path.add_path_constrain(self.z3v_of[lv_z3_name] == ~(self.z3v_of[rv_z3_name]))

            elif isinstance(ir, Unpack):
                ir: Unpack

            elif isinstance(ir, OperationWithLValue) and 'LENGTH' in str(ir):
                ir: Length


            else:
                pass

    def register_z3v(self, v_name: str, v_type: str) -> []:
        if v_name in self.z3v_of:
            if v_name in self.type_constrains_of:
                return [self.type_constrains_of[v_name]]
            else:
                return []
        constrains = []
        if v_type in Uint:
            self.z3v_of[v_name] = BitVec(name=v_name, bv=256)
            if v_name.isnumeric():
                constrains.append(self.z3v_of[v_name] == int(v_name))
            elif '#' in v_name and v_name.split('#')[1].isnumeric():
                constrains.append(self.z3v_of[v_name] == int(v_name.split("#")[1]))
            else:
                constrains.append(UGE(self.z3v_of[v_name], Min_Uint[v_type]))
                constrains.append(ULE(self.z3v_of[v_name], Max_Uint[v_type]))
        elif v_type in Int:
            self.z3v_of[v_name] = BitVec(name=v_name, bv=256)
            if v_name.isnumeric():
                constrains.append(self.z3v_of[v_name] == int(v_name))
            elif '#' in v_name and v_name.split('#')[1].isnumeric():
                constrains.append(self.z3v_of[v_name] == int(v_name.split("#")[1]))
            else:
                constrains.append(self.z3v_of[v_name] >= Min_Int[v_type])
                constrains.append(self.z3v_of[v_name] <= Max_Int[v_type])
        elif v_type == 'bool':
            self.z3v_of[v_name] = Bool(name=v_name)
            if v_name == 'True':
                constrains.append(self.z3v_of[v_name] == True)
            elif '#' in v_name and v_name.split('#')[1] == 'True':
                constrains.append(self.z3v_of[v_name] == True)
            elif v_name == 'False':
                constrains.append(self.z3v_of[v_name] == False)
            elif '#' in v_name and v_name.split('#')[1] == 'False':
                constrains.append(self.z3v_of[v_name] == False)
        elif v_type == 'address':
            self.z3v_of[v_name] = BitVec(name=v_name, bv=256)
        else:
            self.z3v_of[v_name] = BitVec(name=v_name, bv=256)
        if len(constrains) > 0:
            self.type_constrains_of[v_name] = And(constrains)
        return constrains

    def register_random_z3v(self):
        self.random_number_index += 1
        v_name = f'random_{self.random_number_index}'
        self.z3v_of[v_name] = BitVec(name=v_name, bv=256)
        return self.z3v_of[v_name]

    @staticmethod
    def get_first_alias(function: Function, variable_name: str) -> str:
        alias = f'{variable_name}_1'
        if function.entry_point is None:
            return alias
        queue = [function.entry_point]
        idx = 0
        while idx < len(queue):
            node = queue[idx]
            idx += 1
            for ir in node.irs_ssa:
                if isinstance(ir, OperationWithLValue) and ir.lvalue is not None and ir.lvalue.name == variable_name:
                    alias = str(ir.lvalue)
                    return alias
            for son in node.sons:
                queue.append(son)
        return alias

    def analyze_numerical_comparison_relationships(
            self, src: RepairTarget, dest: RepairTarget, op: str, invariants=None
    ) -> bool:
        invariants: List[Invariant]
        if invariants is None:
            invariants = []
        assert src.slither_function_node.full_name == dest.slither_function_node.full_name
        contract_node = src.slither_function_node.contract
        function_node = contract_node.get_function_from_full_name(src.slither_function_node.full_name)
        self.context_id = 0
        paths = []
        self.enumerate_contract_path(
            current_node=function_node.entry_point,
            current_ir_idx=0,
            current_path=ContractPath(),
            paths=paths,
            node_visit_counter={},
            context=self.context_id
        )
        unique_dict = {x.to_string(): x for x in paths}
        paths = list(unique_dict.values())
        for path in paths:
            assert not path.is_finished()
            self.parse_contract_path(path)
        path_constrains = []
        for path in paths:
            path_constrain = path.get_path_constrain()
            if path_constrain is not None:
                path_constrains.append(path_constrain)
        function_constrains = Or(*path_constrains)
        solver = Solver()
        solver.set("timeout", 60000)
        solver.add(function_constrains)
        assert src.ir.lvalue is not None and dest.ir.lvalue is not None
        src_lv_z3_name = f'0#{str(src.ir.lvalue)}'
        dest_lv_z3_name = f'0#{str(dest.ir.lvalue)}'
        assert src_lv_z3_name in self.z3v_of and dest_lv_z3_name in self.z3v_of
        src_lv_z3v = self.z3v_of[src_lv_z3_name]
        dest_lv_z3v = self.z3v_of[dest_lv_z3_name]

        assert op in ['==', '>', '>=', '<=', '<']

        if op == '==':
            proposition = (src_lv_z3v == dest_lv_z3v)
        elif op == '>=':
            proposition = UGE(src_lv_z3v, dest_lv_z3v)
        elif op == '>':
            proposition = UGT(src_lv_z3v, dest_lv_z3v)
        elif op == '<=':
            proposition = ULE(src_lv_z3v, dest_lv_z3v)
        elif op == '<':
            proposition = ULT(src_lv_z3v, dest_lv_z3v)

        solver.push()
        solver.add(proposition)
        if solver.check() == sat:
            proposition_sat = True
        else:
            proposition_sat = False
        solver.pop()

        solver.push()
        solver.add(Not(proposition))
        if solver.check() == unsat:
            not_proposition_sat = False
        else:
            not_proposition_sat = True
        solver.pop()

        return proposition_sat and not not_proposition_sat

    def analyze_numerical_comparison_relationships_2(
            self, src: RepairTarget, dest: RepairTarget, op: str, invariants=None
    ) -> bool:
        invariants: List[Invariant]
        if invariants is None:
            invariants = []
        assert src.slither_function_node.full_name == dest.slither_function_node.full_name

        if str(src.ir.variable_left) == str(dest.ir.lvalue) or str(src.ir.variable_right) == str(dest.ir.lvalue):
            return False

        contract_node = src.slither_function_node.contract
        function_node = contract_node.get_function_from_full_name(src.slither_function_node.full_name)
        self.context_id = 0
        paths = []
        self.enumerate_contract_path(
            current_node=function_node.entry_point,
            current_ir_idx=0,
            current_path=ContractPath(),
            paths=paths,
            node_visit_counter={},
            context=self.context_id
        )
        unique_dict = {x.to_string(): x for x in paths}
        paths = list(unique_dict.values())

        for path in paths:
            assert not path.is_finished()
            self.parse_contract_path(path)

        for path in paths:
            path_constrain = path.get_path_constrain()
            if path_constrain is None:
                continue
            solver = Solver()
            solver.set("timeout", 60000)

            assert src.ir.lvalue is not None and dest.ir.lvalue is not None
            src_lv_z3_name = f'0#{str(src.ir.lvalue)}'
            dest_lv_z3_name = f'0#{str(dest.ir.lvalue)}'
            if src_lv_z3_name not in self.z3v_of or dest_lv_z3_name not in self.z3v_of:
                continue
            src_lv_z3v = self.z3v_of[src_lv_z3_name]
            dest_lv_z3v = self.z3v_of[dest_lv_z3_name]

            def contains_variable(expr, var_name):
                if isinstance(expr, BoolRef) or isinstance(expr, ArithRef):
                    if var_name in str(expr):
                        return True
                    return any(contains_variable(child, var_name) for child in expr.children())
                return False

            if not contains_variable(path_constrain, src_lv_z3_name) or not contains_variable(path_constrain, dest_lv_z3_name):
                continue
            else:
                pass

            def are_equivalent(src, dest, constrain):
                if str(src) == str(dest):
                    return False
                solver = Solver()
                solver.set("timeout", 60000)
                solver.add(constrain)
                if solver.check(src != dest) == sat:
                    return False
                if solver.check(src == dest) == unsat:
                    return False
                return True

            for uncheck_z3v in self.uncheck_z3v_name:
                if uncheck_z3v in self.z3v_of:
                    z3v = self.z3v_of[uncheck_z3v]
                    if (f'0#{src.ir.variable_left}' in self.z3v_of and
                            are_equivalent(self.z3v_of[f'0#{src.ir.variable_left}'], z3v, path_constrain)):
                        return False
                    if (f'0#{src.ir.variable_right}' in self.z3v_of and
                            are_equivalent(self.z3v_of[f'0#{src.ir.variable_right}'], z3v, path_constrain)):
                        return False

            solver.add(path_constrain)
            if solver.check() == sat:
                pass
            else:
                continue

            assert op in ['==', '>', '>=', '<=', '<']

            if op == '==':
                proposition = (src_lv_z3v == dest_lv_z3v)
            elif op == '>=':
                proposition = UGE(src_lv_z3v, dest_lv_z3v)
            elif op == '>':
                proposition = UGT(src_lv_z3v, dest_lv_z3v)
            elif op == '<=':
                proposition = ULE(src_lv_z3v, dest_lv_z3v)
            elif op == '<':
                proposition = ULT(src_lv_z3v, dest_lv_z3v)

            solver.push()
            solver.add(proposition)
            if solver.check() == sat:
                pass
            else:
                return False
            solver.pop()

            solver.push()
            solver.add(Not(proposition))
            if solver.check() == sat:
                return False
            else:
                pass
            solver.pop()

        return True

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
    def group_repair_targets_by_function(
            repair_targets: list[RepairTarget]
    ) -> dict[FunctionContract, list[RepairTarget]]:
        function_repair_targets = defaultdict(list)

        for repair_target in repair_targets:
            function_repair_targets[repair_target.slither_function_node].append(repair_target)

        return function_repair_targets

    def reduce_redundant_repair_targets(self):
        targets = []
        repair_targets_group_by_function = self.group_repair_targets_by_function(self.repair_targets)
        for function in repair_targets_group_by_function:
            repair_targets = repair_targets_group_by_function[function]
            if len(repair_targets) > 1:
                reduced_repair_targets = self.reduce_redundant_repair_targets_in_single_function(repair_targets)
                targets.extend(reduced_repair_targets)
            else:
                targets.extend(repair_targets)
        return targets

    def reduce_redundant_repair_targets_in_single_function_(self, repair_targets: List[RepairTarget]) -> List[RepairTarget]:
        reduced_repair_targets = []

        grouped_targets = defaultdict(list)
        for target in repair_targets:
            key = target.ir.type_str
            grouped_targets[key].append(target)
        for key, targets in grouped_targets.items():

            if len(targets) == 1:
                reduced_repair_targets.append(targets[0])
                continue

            self.uncheck_z3v_name.clear()
            for target in targets:
                target: RepairTarget
                self.uncheck_z3v_name.add(f'0#{str(target.ir.lvalue)}')

            dominators = self.calculate_dominators(targets[0].slither_function_node)
            post_dominators = self.calculate_post_dominators(targets[0].slither_function_node)

            repair_graph = defaultdict(set)
            all_nodes = set()
            for i in range(len(targets)):
                for j in range(len(targets)):
                    src, dest = targets[i], targets[j]
                    if i == j or src.to_string() == dest.to_string():
                        continue
                    if (src.slither_statement_node.node_id in dominators[dest.slither_statement_node.node_id] or
                            src.slither_statement_node.node_id in post_dominators[dest.slither_statement_node.node_id]):
                        op = None
                        if src.ir.type_str in ['+', '*']:
                            op = '>='
                        elif src.ir.type_str == '-':
                            op = '<='
                        else:
                            pass
                        if op is None:
                            continue
                        if self.analyze_numerical_comparison_relationships_2(src, dest, op):
                            repair_graph[src].add(dest)
                            all_nodes.add(src)
                            all_nodes.add(dest)
                    else:
                        pass

            # if repair_graph:
            #     dot = Digraph(comment='Repair Target Dependency Graph')
            #     for node in all_nodes:
            #         dot.node(str(id(node)), node.to_string(), shape='box')
            #     for src, dests in repair_graph.items():
            #         for dest in dests:
            #             dot.edge(str(id(src)), str(id(dest)))
            #     dot.render('RepairTargetDependencyGraph', format='png', cleanup=True)

            if repair_graph:
                reduced_repair_targets.extend(
                    self.find_min_repair_targets_from_repair_target_dependency_graph(set(targets), repair_graph)
                )
            else:
                reduced_repair_targets.extend(targets)

        return reduced_repair_targets

    def reduce_redundant_repair_targets_in_single_function(self, repair_targets: List[RepairTarget]) -> List[RepairTarget]:
        reduced_repair_targets = []

        grouped_targets = defaultdict(list)
        for target in repair_targets:
            key = target.ir.type_str
            grouped_targets[key].append(target)
        for key, targets in grouped_targets.items():
            if len(targets) == 1:
                reduced_repair_targets.append(targets[0])
                continue

            self.uncheck_z3v_name.clear()
            for target in targets:
                self.uncheck_z3v_name.add(f'0#{str(target.ir.lvalue)}')

            dominators = self.calculate_dominators(targets[0].slither_function_node)
            post_dominators = self.calculate_post_dominators(targets[0].slither_function_node)

            dominance_graph = defaultdict(set)
            comparison_graph = defaultdict(set)
            all_nodes = set()

            for i in range(len(targets)):
                for j in range(len(targets)):
                    src, dest = targets[i], targets[j]
                    if i == j or src.to_string() == dest.to_string():
                        continue

                    if (src.slither_statement_node.node_id in dominators[dest.slither_statement_node.node_id] or
                            src.slither_statement_node.node_id in post_dominators[dest.slither_statement_node.node_id]):
                        dominance_graph[src].add(dest)
                        all_nodes.add(src)
                        all_nodes.add(dest)
                    else:
                        pass

                    op = None
                    if src.ir.type_str in ['+', '*']:
                        op = '>='
                    elif src.ir.type_str == '-':
                        op = '<='

                    if op and self.analyze_numerical_comparison_relationships_2(src, dest, op):
                        comparison_graph[src].add(dest)
                        all_nodes.add(src)
                        all_nodes.add(dest)

            # if dominance_graph or comparison_graph:
            #     dot = Digraph(comment='Repair Target Dependency Graph')
            #     for node in all_nodes:
            #         dot.node(str(id(node)), node.to_string(), shape='box')
            #     for src, dests in dominance_graph.items():
            #         for dest in dests:
            #             dot.edge(str(id(src)), str(id(dest)), label='dom', style='solid')
            #     for src, dests in comparison_graph.items():
            #         for dest in dests:
            #             dot.edge(str(id(src)), str(id(dest)), label='comp', style='dashed')
            #     dot.render('RepairTargetDependencyGraph', format='png', cleanup=True)

            repair_graph = defaultdict(set)
            for src in dominance_graph:
                for dest in dominance_graph[src]:
                    if dest in comparison_graph.get(src, set()):
                        repair_graph[src].add(dest)

            if repair_graph:
                reduced_repair_targets.extend(
                    self.find_min_repair_targets_from_repair_target_dependency_graph(set(targets), repair_graph)
                )
            else:
                reduced_repair_targets.extend(targets)


        return reduced_repair_targets

    @staticmethod
    def find_min_repair_targets_from_repair_target_dependency_graph(
            all_targets: Set[RepairTarget],
            graph: Union[Dict[int, Set[RepairTarget]], DefaultDict[int, Set[RepairTarget]]]  # A: {B, C} 意味着A有指向B和C的边
    ) -> Set[RepairTarget]:
        selected_repair_targets = set()
        remaining_targets = set(all_targets)

        while remaining_targets:

            in_degree = {node: 0 for node in remaining_targets}
            for src in graph:
                for dest in graph[src]:
                    if dest in remaining_targets:
                        in_degree[dest] += 1

            if any(deg == 0 for deg in in_degree.values()):
                queue = deque()
                visited = set()
                for node in in_degree:
                    if in_degree[node] == 0:
                        queue.append(node)
                        visited.add(node)
                        selected_repair_targets.add(node)
                while queue:
                    src_node = queue.popleft()
                    remaining_targets.remove(src_node)
                    for dest_node in graph[src_node]:
                        if dest_node in visited:
                            continue
                        queue.append(dest_node)
                        visited.add(dest_node)

            else:
                influence_count = {node: 0 for node in remaining_targets}
                for node in remaining_targets:
                    queue = deque()
                    visited = set()
                    queue.append(node)
                    visited.add(node)
                    while queue:
                        src_node = queue.popleft()
                        for dest_node in graph[src_node]:
                            if dest_node in visited:
                                continue
                            influence_count[src_node] += 1
                            queue.append(dest_node)
                            visited.add(dest_node)

                max_node = max(
                    influence_count,
                    key=lambda node: (influence_count[node], -node.get_line_number())
                )

                queue = deque()
                visited = set()
                queue.append(max_node)
                visited.add(max_node)
                selected_repair_targets.add(max_node)
                while queue:
                    src_node = queue.popleft()
                    remaining_targets.remove(src_node)
                    for dest_node in graph[src_node]:
                        if dest_node in visited:
                            continue
                        queue.append(dest_node)
                        visited.add(dest_node)

            for target in all_targets:
                if target not in remaining_targets and target in graph:
                    del graph[target]
                    for node in graph:
                        if target in graph[node]:
                            graph[node].remove(target)

        return selected_repair_targets
