from typing import Optional, List

from slither import Slither
from slither.core.cfg.node import Node
from slither.core.declarations import FunctionContract
from slither.slithir.operations import Operation
from z3 import *

z3v_cnt = 0


def define_variable(v_name, v_type):
    global z3v_cnt
    if v_type == 'Int':
        z3v_cnt += 1
        return Int(v_name + '@' + str(z3v_cnt))
    elif v_type == 'Bool':
        z3v_cnt += 1
        return Bool(v_name + '@' + str(z3v_cnt))


def ge(v1, v2):
    return v1 >= v2


def gt(v1, v2):
    return v1 > v2


def le(v1, v2):
    return v1 <= v2


def lt(v1, v2):
    return v1 < v2


def eq(v1, v2):
    return v1 == v2


def ne(v1, v2):
    return v1 != v2


def _and(exp1, exp2):
    return And(exp1, exp2)


def _ands(_exps: []):
    return And(_exps)


def _or(exp1, exp2):
    return Or(exp1, exp2)


def _ors(_exps: []):
    return Or(_exps)


def _add(exp1, exp2):
    return exp1 + exp2


def _mul(exp1, exp2):
    return exp1 * exp2


def _div(exp1, exp2):
    return exp1 / exp2


def _sub(exp1, exp2):
    return exp1 - exp2


def _mod(exp1, exp2):
    return exp1 % exp2


class SafeMathFinderSMT:
    def __init__(self, slither: Slither):
        self.reusable = {}
        self.slither = slither
        self.target_types = ['uint8', 'uint16', 'uint24', 'uint32', 'uint40', 'uint48', 'uint56', 'uint64', 'uint72',
                             'uint80',
                             'uint88', 'uint96', 'uint104', 'uint112', 'uint120', 'uint128', 'uint136', 'uint144',
                             'uint152',
                             'uint160', 'uint168', 'uint176', 'uint184', 'uint192', 'uint200', 'uint208', 'uint216',
                             'uint224',
                             'uint232', 'uint240', 'uint248', 'uint256']
        self.min_of = {'uint8': 0, 'uint16': 0, 'uint24': 0, 'uint32': 0, 'uint40': 0, 'uint48': 0,
                       'uint56': 0, 'uint64': 0, 'uint72': 0, 'uint80': 0, 'uint88': 0, 'uint96': 0,
                       'uint104': 0, 'uint112': 0, 'uint120': 0, 'uint128': 0, 'uint136': 0, 'uint144': 0,
                       'uint152': 0, 'uint160': 0, 'uint168': 0, 'uint176': 0, 'uint184': 0, 'uint192': 0,
                       'uint200': 0, 'uint208': 0, 'uint216': 0, 'uint224': 0, 'uint232': 0, 'uint240': 0,
                       'uint248': 0, 'uint256': 0}
        self.max_bit_of = {'uint8': 8, 'uint16': 16, 'uint24': 24, 'uint32': 32,
                           'uint40': 40, 'uint48': 48, 'uint56': 56,
                           'uint64': 64, 'uint72': 72, 'uint80': 80,
                           'uint88': 88, 'uint96': 96, 'uint104': 104,
                           'uint112': 112, 'uint120': 120, 'uint128': 128,
                           'uint136': 136, 'uint144': 144, 'uint152': 152,
                           'uint160': 160, 'uint168': 168, 'uint176': 176,
                           'uint184': 184, 'uint192': 192, 'uint200': 200,
                           'uint208': 208, 'uint216': 216, 'uint224': 224,
                           'uint232': 232, 'uint240': 240, 'uint248': 248,
                           'uint256': 256}
        self.ERROR = False
        self.ERROR_MSG = ''

    def structural_judgement(self) -> List[FunctionContract]:
        candidates = []
        for contract in self.slither.contracts:
            contract_kind = str(contract.contract_kind)
            if contract_kind != 'contract' and contract_kind != 'library':
                continue
            for function in contract.functions:
                if len(function.parameters) != 2 or len(function.returns) != 1:
                    continue
                param_1_type = str(function.parameters[0].type)
                param_2_type = str(function.parameters[1].type)
                return_type = str(function.returns[0].type)
                if param_1_type != param_2_type or param_1_type != return_type or return_type not in self.target_types:
                    continue
                if len(function.state_variables_read) != 0 or len(function.state_variables_written) != 0:
                    continue
                candidates.append(function)
        return candidates

    @staticmethod
    def get_starts_and_ends(function: FunctionContract):
        starts = []
        ends = []
        for node in function.nodes:
            if len(node.sons) == 0:
                ends.append(node)
            if len(node.fathers) == 0:
                starts.append(node)
        return starts, ends

    @staticmethod
    def get_all_variables(function: FunctionContract) -> (List[str], List[str]):
        variables = []
        types = []
        for var in function.variables:
            if str(var) != '':
                variables.append(str(var.name))
                types.append(str(var.type))
        for node in function.nodes:
            for var in node.slithir_variables:
                variables.append(str(var.name))
                types.append(str(var.type))
        return variables, types

    def get_all_paths(self, function: FunctionContract) -> List[List[Node]]:
        paths = []
        path_stk = []

        def dfs(start: Node, end: Node):
            if start == end:
                paths.append(path_stk[:])
                return
            for node in start.sons:
                path_stk.append(node)
                dfs(node, end)
                path_stk.pop()

        starts, ends = self.get_starts_and_ends(function)
        for s in starts:
            for ed in ends:
                path_stk.clear()
                path_stk.append(s)
                dfs(s, ed)
        return paths

    @staticmethod
    def get_path_irs(path: [Node]) -> List[str]:
        irs = []
        for i in range(0, len(path)):
            for ir in path[i].irs:
                if 'CONDITION' in str(ir):
                    if i < len(path) - 1 and path[i].son_true == path[i + 1]:
                        irs.append(str(ir) + ' True')
                    elif i < len(path) - 1 and path[i].son_false == path[i + 1]:
                        irs.append(str(ir) + ' False')
                else:
                    irs.append(str(ir))
        return irs

    @staticmethod
    def get_path_slithir(path: List[Node]) -> List[Operation]:
        irs = []
        for path_node in path:
            for ir in path_node.irs:
                irs.append(ir)
        return irs

    def functional_judgement(self, function: FunctionContract):
        solver = Solver()
        solver.set('timeout', 60000)
        variables_name, variables_type = self.get_all_variables(function)
        p1_z3v = define_variable('p1_z3v', 'Int')
        p2_z3v = define_variable('p2_z3v', 'Int')
        return_z3v = define_variable('return_z3v', 'Int')
        type_of = {}
        z3_variable_of = {}
        for i in range(0, len(variables_name)):
            type_of[variables_name[i]] = variables_type[i]
            if variables_type[i] == 'bool':
                z3_variable_of[variables_name[i]] = define_variable(variables_name[i], 'Bool')
            elif 'int' in variables_type[i]:
                z3_variable_of[variables_name[i]] = define_variable(variables_name[i], 'Int')
        solver.add(eq(p1_z3v, z3_variable_of[function.parameters[0].name]))
        solver.add(eq(p2_z3v, z3_variable_of[function.parameters[1].name]))
        if function.returns[0].name in variables_name:
            solver.add(eq(return_z3v, z3_variable_of[function.returns[0].name]))
        function_constraint = self.get_function_constraint(function, return_z3v, variables_name,
                                                           z3_variable_of, str(function.returns[0].type))
        if function_constraint is not None:
            solver.add(function_constraint)
        type_constraints = self.get_type_constraint(variables_name, type_of, z3_variable_of, p1_z3v, p2_z3v, return_z3v,
                                                    str(function.returns[0].type))
        for type_constraint in type_constraints:
            solver.add(type_constraint)
        if solver.check(return_z3v != p1_z3v + p2_z3v) == unsat:
            return True, '+@' + str(function.returns[0].type)
        elif solver.check(return_z3v != p1_z3v - p2_z3v) == unsat:
            return True, '-@' + str(function.returns[0].type)
        elif solver.check(return_z3v != p2_z3v - p1_z3v) == unsat:
            return True, 'SAFE_SUB_2@' + str(function.returns[0].type)
        elif solver.check(return_z3v != p1_z3v * p2_z3v) == unsat:
            return True, '*@' + str(function.returns[0].type)
        elif solver.check(return_z3v != p1_z3v / p2_z3v) == unsat:
            return True, '/@' + str(function.returns[0].type)
        elif solver.check(return_z3v != p2_z3v / p1_z3v) == unsat:
            return True, 'SAFE_DIV_2@' + str(function.returns[0].type)
        return False, self.ERROR_MSG if self.ERROR_MSG != '' else ''

    def get_type_constraint(self, variables_name, variables_type, z3_variable_of, p1z3v, p2z3v, return_z3v,
                            return_type):
        constraints = []
        for variable in variables_name:
            if 'int' not in variables_type[variable]:
                continue
            constraints.append(ge(z3_variable_of[variable], self.min_of[variables_type[variable]]))
            constraints.append(lt(z3_variable_of[variable], 2 ** self.max_bit_of[variables_type[variable]]))
        constraints.append(ge(p1z3v, self.min_of[return_type]))
        constraints.append(lt(p1z3v, 2 ** self.max_bit_of[return_type]))
        constraints.append(ge(p2z3v, self.min_of[return_type]))
        constraints.append(lt(p2z3v, 2 ** self.max_bit_of[return_type]))
        constraints.append(ge(return_z3v, self.min_of[return_type]))
        constraints.append(lt(return_z3v, 2 ** self.max_bit_of[return_type]))
        return constraints

    def get_function_constraint(self, function: FunctionContract, return_z3v,
                                variables_name, z3_variable_of, return_type):
        function_constraints = []
        max_ = 2 ** 256 - 1
        if return_type is not None:
            max_ = 2 ** self.max_bit_of[return_type] - 1
        paths = self.get_all_paths(function)
        for path in paths:
            path_constraints = []
            revert = False
            irs = self.get_path_irs(path)
            for ir in irs:
                if revert:
                    break
                tokens = ir.split(' ')
                if len(tokens) == 3 and ':=' in ir and tokens[0].split('(')[0] in variables_name:
                    if '(' in tokens[0] and ')' in tokens[0]:
                        lv = tokens[0].split('(')[0]
                    else:
                        lv = tokens[0]
                    if str(lv).isdecimal():
                        lv = int(lv)
                    elif lv not in variables_name:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + lv
                        return False, self.ERROR_MSG
                    lv = z3_variable_of[lv] if lv in z3_variable_of else lv
                    if '(' in tokens[2] and ')' in tokens[2]:
                        rv = tokens[2].split('(')[0]
                    else:
                        rv = tokens[2]
                    if str(rv).isdecimal():
                        rv = int(rv)
                    elif rv not in variables_name:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + rv
                        return False, self.ERROR_MSG
                    rv = z3_variable_of[rv] if rv in z3_variable_of else rv
                    path_constraints.append(eq(lv, rv))
                elif len(tokens) == 5 and '=' in ir and tokens[3] in ['+', '-', '*', '/', '%']:
                    if '(' in tokens[0] and ')' in tokens[0]:
                        lv = tokens[0].split('(')[0]
                    else:
                        lv = tokens[0]
                    if str(lv).isdecimal():
                        lv = int(lv)
                    elif lv not in variables_name:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + lv
                        return False, self.ERROR_MSG
                    lv = z3_variable_of[lv] if lv in z3_variable_of else lv
                    if '(' in tokens[2] and ')' in tokens[2]:
                        rv1 = tokens[2].split('(')[0]
                    else:
                        rv1 = tokens[2]
                    if str(rv1).isdecimal():
                        rv1 = int(rv1)
                    elif rv1 not in variables_name:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + rv1
                        return False, self.ERROR_MSG
                    rv1 = z3_variable_of[rv1] if rv1 in z3_variable_of else rv1
                    if '(' in tokens[4] and ')' in tokens[4]:
                        rv2 = tokens[4].split('(')[0]
                    else:
                        rv2 = tokens[4]
                    if str(rv2).isdecimal():
                        rv2 = int(rv2)
                    elif rv2 not in variables_name:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + rv2
                        return False, self.ERROR_MSG
                    rv2 = z3_variable_of[rv2] if rv2 in z3_variable_of else rv2
                    if tokens[3] == '+':

                        path_constraints.append(eq(lv, _mod(_add(rv1, rv2), _add(max_, 1))))
                    elif tokens[3] == '-':
                        path_constraints.append(eq(lv, _mod(_add(_sub(rv1, rv2), _add(max_, 1)),
                                                            _add(max_, 1))))
                    elif tokens[3] == '*':
                        path_constraints.append(eq(lv, _mod(_mul(rv1, rv2), _add(max_, 1))))
                    elif tokens[3] == '/':
                        path_constraints.append(eq(lv, _div(rv1, rv2)))
                    elif tokens[3] == '%':
                        path_constraints.append(eq(lv, _mod(rv1, rv2)))
                elif len(tokens) == 5 and '=' in ir and tokens[3] in ['==', '>', '>=', '<', '<=', '!=', '||', '&&']:
                    if '(' in tokens[0] and ')' in tokens[0]:
                        lv = tokens[0].split('(')[0]
                    else:
                        lv = tokens[0]
                    if str(lv).isdecimal():
                        lv = int(lv)
                    elif lv not in variables_name:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + lv
                        return False, self.ERROR_MSG
                    lv = z3_variable_of[lv] if lv in z3_variable_of else lv
                    if '(' in tokens[2] and ')' in tokens[2]:
                        rv1 = tokens[2].split('(')[0]
                    else:
                        rv1 = tokens[2]
                    if str(rv1).isdecimal():
                        rv1 = int(rv1)
                    elif rv1 not in variables_name:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + rv1
                        return False, self.ERROR_MSG
                    rv1 = z3_variable_of[rv1] if rv1 in z3_variable_of else rv1
                    if '(' in tokens[4] and ')' in tokens[4]:
                        rv2 = tokens[4].split('(')[0]
                    else:
                        rv2 = tokens[4]
                    if str(rv2).isdecimal():
                        rv2 = int(rv2)
                    elif rv2 not in variables_name:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + rv2
                        return False, self.ERROR_MSG
                    rv2 = z3_variable_of[rv2] if rv2 in z3_variable_of else rv2
                    if tokens[3] == '==':
                        path_constraints.append(eq(lv, eq(rv1, rv2)))
                    elif tokens[3] == '>=':
                        path_constraints.append(eq(lv, ge(rv1, rv2)))
                    elif tokens[3] == '<=':
                        path_constraints.append(eq(lv, le(rv1, rv2)))
                    elif tokens[3] == '>':
                        path_constraints.append(eq(lv, gt(rv1, rv2)))
                    elif tokens[3] == '<':
                        path_constraints.append(eq(lv, lt(rv1, rv2)))
                    elif tokens[3] == '!=':
                        path_constraints.append(eq(lv, ne(rv1, rv2)))
                    elif tokens[3] == '||':
                        path_constraints.append(eq(lv, _or(rv1, rv2)))
                    elif tokens[3] == '&&':
                        path_constraints.append(eq(lv, _and(rv1, rv2)))
                elif '=' in ir and tokens[2] == 'SOLIDITY_CALL' and \
                        ('assert(bool)' in tokens[3] or 'require(bool)' in tokens[3] or 'require(bool,string)' in
                         tokens[3] or 'revert' in tokens[3]):
                    cond = None
                    if 'assert(bool)' in tokens[3]:
                        cond = tokens[3].split('assert(bool)(')[1].split(')')[0]
                    elif 'require(bool)' in tokens[3]:
                        cond = tokens[3].split('require(bool)(')[1].split(')')[0]
                    elif 'require(bool,string)' in tokens[3]:
                        cond = tokens[3].split('require(bool,string)(')[1].split(',')[0]
                    elif 'revert' in tokens[3]:
                        revert = True
                        continue
                    if cond is None or cond not in z3_variable_of:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + str(cond)
                        return False, self.ERROR_MSG
                    cond = z3_variable_of[cond]
                    path_constraints.append(eq(cond, True))
                elif ' = INTERNAL_CALL, ' in ir:
                    sub_call_constraint = []
                    tokens = ir.split(' = INTERNAL_CALL, ')
                    target_contract_name = tokens[1].split('.')[0]
                    target_function_name = tokens[1].split('.')[1].split('(')[0]
                    receiver_z3v = z3_variable_of[tokens[0].split('(')[0]]
                    receiver_type = tokens[0].split('(')[1].replace(')', '')
                    parameters_name = tokens[1].split('(')[2].replace(')', '').split(',')
                    parameters_type = tokens[1].split('(')[1].replace(')', '').split(',')
                    target_function = self.get_function_node(target_contract_name, target_function_name,
                                                             parameters_type)
                    if (len(target_function.state_variables_read) != 0 or
                            len(target_function.state_variables_written) != 0 or len(target_function.returns) != 1):
                        continue
                    if target_function == function:
                        continue
                    target_function_parameters_name = []
                    for param in target_function.parameters:
                        target_function_parameters_name.append(param.name)
                    assert len(target_function.returns) == 1
                    target_function_return_name = target_function.returns[0].name
                    params, typs = self.get_all_variables(target_function)
                    sub_call_type_of = {}
                    sub_call_z3_variable_of = {}
                    for i in range(0, len(params)):
                        sub_call_type_of[params[i]] = typs[i]
                        if typs[i] == 'bool':
                            sub_call_z3_variable_of[params[i]] = define_variable(params[i], 'Bool')
                        elif 'int' in typs[i]:
                            sub_call_z3_variable_of[params[i]] = define_variable(params[i], 'Int')
                    if target_function_return_name != '' and target_function_return_name in sub_call_z3_variable_of:
                        sub_call_constraint.append(
                            eq(receiver_z3v, sub_call_z3_variable_of[target_function_return_name]))
                    for i in range(0, len(parameters_name)):
                        if ((parameters_type[i] == 'bool' or 'int' in parameters_type[i])
                                and parameters_name[i] in z3_variable_of):
                            sub_call_constraint.append(eq(z3_variable_of[parameters_name[i]],
                                                          sub_call_z3_variable_of[target_function_parameters_name[i]]))
                    for variable in params:
                        if 'int' not in sub_call_type_of[variable]:
                            continue
                        sub_call_constraint.append(
                            ge(sub_call_z3_variable_of[variable], self.min_of[sub_call_type_of[variable]]))
                        sub_call_constraint.append(
                            lt(sub_call_z3_variable_of[variable], 2 ** self.max_bit_of[sub_call_type_of[variable]]))
                    sub_call_constraint.append(
                        self.get_function_constraint(target_function, receiver_z3v, params, sub_call_z3_variable_of,
                                                     receiver_type))
                    path_constraints.append(_ands(sub_call_constraint))
                elif 'INTERNAL_CALL, ' in ir:
                    sub_call_constraint = []
                    tokens = ir.split('INTERNAL_CALL, ')
                    target_contract_name = tokens[1].split('.')[0]
                    target_function_name = tokens[1].split('.')[1].split('(')[0]
                    parameters_name = tokens[1].split('(')[2].replace(')', '').split(',')
                    parameters_type = tokens[1].split('(')[1].replace(')', '').split(',')
                    target_function = self.get_function_node(target_contract_name, target_function_name,
                                                             parameters_type)
                    if len(target_function.state_variables_read) != 0 or len(
                            target_function.state_variables_written) != 0:
                        continue
                    if target_function == function:
                        continue
                    target_function_parameters_name = []
                    for param in target_function.parameters:
                        target_function_parameters_name.append(param.name)
                    params, typs = self.get_all_variables(target_function)
                    sub_call_type_of = {}
                    sub_call_z3_variable_of = {}
                    for i in range(0, len(params)):
                        sub_call_type_of[params[i]] = typs[i]
                        if typs[i] == 'bool':
                            sub_call_z3_variable_of[params[i]] = define_variable(params[i], 'Bool')
                        elif 'int' in typs[i]:
                            sub_call_z3_variable_of[params[i]] = define_variable(params[i], 'Int')
                    for i in range(0, len(parameters_name)):
                        if ((parameters_type[i] == 'bool' or 'int' in parameters_type[i])
                                and parameters_name[i] in z3_variable_of):
                            sub_call_constraint.append(eq(z3_variable_of[parameters_name[i]],
                                                          sub_call_z3_variable_of[target_function_parameters_name[i]]))
                    for variable in params:
                        if 'int' not in sub_call_type_of[variable]:
                            continue
                        sub_call_constraint.append(
                            ge(sub_call_z3_variable_of[variable], self.min_of[sub_call_type_of[variable]]))
                        sub_call_constraint.append(
                            lt(sub_call_z3_variable_of[variable], 2 ** self.max_bit_of[sub_call_type_of[variable]]))
                    sub_call_constraint.append(
                        self.get_function_constraint(target_function, None, params, sub_call_z3_variable_of,
                                                     None))
                    path_constraints.append(_ands(sub_call_constraint))
                elif len(tokens) == 2 and tokens[0] == 'RETURN':
                    if str(tokens[1]).isdecimal():
                        path_constraints.append(eq(return_z3v, int(tokens[1])))
                    elif tokens[1] in z3_variable_of:
                        path_constraints.append(eq(return_z3v, z3_variable_of[tokens[1]]))
                    else:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + str(tokens[1])
                        return False, self.ERROR_MSG
                elif len(tokens) == 3 and tokens[0] == 'CONDITION' and tokens[2] in ['True', 'False']:
                    if tokens[1] not in z3_variable_of:
                        self.ERROR = True
                        self.ERROR_MSG = 'unknown variable: ' + str(tokens[1])
                        return False, self.ERROR_MSG
                    if tokens[2] == 'True':
                        path_constraints.append(eq(z3_variable_of[tokens[1]], True))
                    else:
                        path_constraints.append(eq(z3_variable_of[tokens[1]], False))
                else:
                    self.ERROR = True
                    self.ERROR_MSG = 'Unresolved IR: ' + ir
            if not revert and len(path_constraints) != 0:
                function_constraints.append(_ands(path_constraints))
        return _ors(function_constraints) if len(function_constraints) > 0 else None

    def get_inter_procedure_constraint(self):
        return

    @staticmethod
    def has_circle(function_node: FunctionContract) -> bool:
        in_degree = {}
        for node in function_node.nodes:
            if node.node_id not in in_degree:
                in_degree[node.node_id] = 0
        for node in function_node.nodes:
            for dest in node.sons:
                in_degree[dest.node_id] += 1
        stk = []
        cnt = 0
        for node in function_node.nodes:
            if in_degree[node.node_id] == 0:
                cnt += 1
                stk.append(node)
        while len(stk) > 0:
            cur = stk.pop()
            for son in cur.sons:
                in_degree[son.node_id] -= 1
                if in_degree[son.node_id] == 0:
                    cnt += 1
                    stk.append(son)
        return cnt != len(function_node.nodes)

    def get_function_node(self, contract_name, function_name, parameters_type: [str]) -> Optional[FunctionContract]:
        for contract in self.slither.contracts:
            if contract.name == contract_name:
                for function in contract.functions:
                    if function.name == function_name and len(function.parameters) == len(parameters_type):
                        found = True
                        for i in range(0, len(parameters_type)):
                            if parameters_type[i] != str(function.parameters[i].type):
                                found = False
                        if found:
                            return function
        return None
