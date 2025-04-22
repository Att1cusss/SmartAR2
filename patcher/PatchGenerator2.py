import os
from collections import defaultdict
from typing import List, Dict, Optional, Union

from py_solidity_parser.nodes import IterableNodeBase, NodeBase
from slither import Slither
from slither.core.declarations import FunctionContract, Contract
from slither.core.solidity_types.elementary_type import Uint, Int

from PathConfig import CONTRACTS_DIR
from patcher.template import Template
from utils.entity.RepairTarget import RepairTarget


class PatchGenerator2:
    def __init__(self, repair_targets: List[RepairTarget],
                 contract_source_code: str, slither: Slither, source_root,
                 reusable_safemath_functions):
        self.contract_source_code = contract_source_code
        self.slither = slither
        self.source_root = source_root

        self.repair_targets_of_line = defaultdict(list)
        for target in repair_targets:
            self.repair_targets_of_line[target.get_line_number()].append(target)
        for line_number, target_list in self.repair_targets_of_line.items():
            target_list.sort(key=lambda x: len(x.ast_node.extract_code(self.contract_source_code, False)))

        self.reusable_safemath_functions = reusable_safemath_functions
        self.template = Template()

        self.additional_library_name = 'SmartAR'
        self.additional_library_code = 'contract ' + self.additional_library_name + ' {'
        self.son_of_additional_library = set()
        self.name_of_operator = {'+': 'add', '-': 'sub', '*': 'mul', '/': 'div'}
        self.operator_of = {
            '+': '+',
            '++': '+',
            '+=': '+',
            '-': '-',
            '--': '-',
            '-=': '-',
            '*': '*',
            '*=': '*',
            '/': '/',
            '/=': '/'
        }
        self.additional_library_function_types = set()
        self.additional_inherit_relation_ship = []
        self.additional_using_relation_ship = []

        self.replacements = {}

        self.contract_type = {}
        for contract in slither.contracts:
            contract_kind = str(contract.contract_kind)
            if contract_kind != 'contract' and contract_kind != 'library':
                continue
            self.contract_type[contract.name] = contract_kind
        self.contract_type[self.additional_library_name] = 'contract'

        self.inheritance_graph = {}

        self.fixed_contract_path = os.path.join(CONTRACTS_DIR, 'fixed.sol')

        self.contract_usable_safe_function = {}

    def process(self):
        self.init()
        for line in sorted(self.repair_targets_of_line):
            try:
                self.patch_line(line)
            except Exception as e:
                continue
        fixed_source_code = self.get_additional_library_code() + self.get_modified_source_code()
        with open(self.fixed_contract_path, 'w', encoding='utf-8') as f:
            f.write(fixed_source_code)

    def init(self):
        for safe_function_type in self.reusable_safemath_functions:
            for safe_function in self.reusable_safemath_functions[safe_function_type]:
                safe_function: FunctionContract
                if safe_function.contract.is_library:
                    continue
                if safe_function.contract.name not in self.contract_usable_safe_function:
                    self.contract_usable_safe_function[safe_function.contract.name] = {}
                if safe_function_type not in self.contract_usable_safe_function[safe_function.contract.name]:
                    self.contract_usable_safe_function[safe_function.contract.name][safe_function_type] = \
                        {
                            'safe_function_name': safe_function.name,
                            'safe_contract_type': 'contract'
                        }
                for contract in self.slither.contracts:
                    for inherit in contract.inheritance:
                        if inherit.name == safe_function.contract.name:
                            if contract.name not in self.contract_usable_safe_function:
                                self.contract_usable_safe_function[contract.name] = {}
                            if safe_function_type not in self.contract_usable_safe_function[contract.name]:
                                self.contract_usable_safe_function[contract.name][safe_function_type] = \
                                    {
                                        'safe_function_name': safe_function.name,
                                        'safe_contract_type': 'contract'
                                    }

    def patch_line(self, line_number):
        repair_targets = self.repair_targets_of_line[line_number]
        repair_targets: List[RepairTarget]
        replacement = []

        for repair_target in repair_targets:
            ast_node = repair_target.ast_node

            bug_code = ast_node.extract_code(self.contract_source_code, False)
            for replace_rule in replacement:
                bug_code = str(bug_code).replace(replace_rule['bug'], replace_rule['fixed'])

            operator = ast_node.operator
            operand_data_type = ast_node.typeDescriptions['typeString']
            safe_function_type = f'{self.operator_of[operator]}@{operand_data_type}'
            self.get_safemath_function(repair_target, safe_function_type)
            fixed_code = self.get_fixed_code(repair_target, safe_function_type, replacement)

            if fixed_code != '':
                replacement.append({'bug': bug_code, 'fixed': fixed_code})

        self.replacements[line_number] = replacement

    def get_safemath_function(self, repair_target: RepairTarget, safe_function_type: str):
        repair_target_contract_name = repair_target.slither_function_node.contract.name
        if repair_target_contract_name in self.contract_usable_safe_function and \
                safe_function_type in self.contract_usable_safe_function[repair_target_contract_name]:
            return

        elif safe_function_type in self.reusable_safemath_functions and \
                len(self.reusable_safemath_functions[safe_function_type]) > 0 and \
                any(f.contract.is_library for f in self.reusable_safemath_functions[safe_function_type]):
            library = next(
                (f for f in self.reusable_safemath_functions[safe_function_type] if f.contract.is_library),
                None
            )
            library: FunctionContract
            self.register_available_safemath(repair_target, safe_function_type, library)
            return

        elif safe_function_type in self.reusable_safemath_functions and \
                len(self.reusable_safemath_functions[safe_function_type]) > 0 and \
                not any(f.contract.is_library for f in self.reusable_safemath_functions[safe_function_type]):
            picked_safemath_function = None
            for safemath_function in self.reusable_safemath_functions[safe_function_type]:
                safemath_function: FunctionContract
                if not self.will_cause_circular_inheritance(repair_target.slither_function_node.contract, safemath_function.contract):
                    picked_safemath_function = safemath_function
                    break
            if picked_safemath_function is not None:
                picked_safemath_function: FunctionContract
                self.register_available_safemath(repair_target, safe_function_type, picked_safemath_function)
                return
        self.register_available_safemath(repair_target, safe_function_type, None)

    def register_available_safemath(
            self, repair_target: RepairTarget, safe_function_type, safe_function: Optional[FunctionContract]
    ):
        repair_target_contract_name = repair_target.slither_function_node.contract.name
        safe_function: FunctionContract
        if safe_function is None:
            self.additional_library_function_types.add(safe_function_type)
            if repair_target_contract_name not in self.son_of_additional_library and \
                    {repair_target_contract_name: self.additional_library_name} not in self.additional_inherit_relation_ship:
                self.additional_inherit_relation_ship.append({repair_target_contract_name: self.additional_library_name})
            if repair_target_contract_name not in self.contract_usable_safe_function:
                self.contract_usable_safe_function[repair_target_contract_name] = {}
            operand_data_type = safe_function_type.split('@')[1]
            self.contract_usable_safe_function[repair_target_contract_name][safe_function_type] = {
                'safe_function_name': f'{self.name_of_operator[self.operator_of[repair_target.ast_node.operator]]}_{operand_data_type}',
                'safe_contract_type': 'contract'
            }
            for contract in repair_target.slither_function_node.contract.derived_contracts:
                self.son_of_additional_library.add(contract.name)
                if contract.name not in self.contract_usable_safe_function:
                    self.contract_usable_safe_function[contract.name] = {}
                if safe_function_type not in self.contract_usable_safe_function[contract.name]:
                    self.contract_usable_safe_function[contract.name][safe_function_type] = {
                        'safe_function_name': f'{self.name_of_operator[self.operator_of[repair_target.ast_node.operator]]}_{operand_data_type}',
                        'safe_contract_type': 'contract'
                    }
            return
        if safe_function.contract.is_library:
            self.additional_using_relation_ship.append(
                {repair_target_contract_name: f'{safe_function.contract.name}@{safe_function_type.split("@")[1]}'}
            )
            if repair_target_contract_name not in self.contract_usable_safe_function:
                self.contract_usable_safe_function[repair_target_contract_name] = {}
            self.contract_usable_safe_function[repair_target_contract_name][safe_function_type] = {
                'safe_function_name': safe_function.name,
                'safe_contract_type': 'library'
            }
        else:
            if {{repair_target_contract_name: safe_function.contract.name}} not in self.additional_inherit_relation_ship:
                self.additional_inherit_relation_ship.append({repair_target_contract_name: safe_function.contract.name})
            if repair_target_contract_name not in self.contract_usable_safe_function:
                self.contract_usable_safe_function[repair_target_contract_name] = {}
            self.contract_usable_safe_function[repair_target_contract_name][safe_function_type] = {
                'safe_function_name': safe_function.name,
                'safe_contract_type': 'contract'
            }
            for contract in repair_target.slither_function_node.contract.derived_contracts:
                if contract.name not in self.contract_usable_safe_function:
                    self.contract_usable_safe_function[contract.name] = {}
                if safe_function_type not in self.contract_usable_safe_function[contract.name]:
                    self.contract_usable_safe_function[contract.name][safe_function_type] = {
                        'safe_function_name': safe_function.name,
                        'safe_contract_type': 'contract'
                    }

    def get_fixed_code(self, repair_target: RepairTarget, safe_function_type: str, replacement: List[Dict]):
        repair_target_contract_name = repair_target.slither_function_node.contract.name
        ast_node = repair_target.ast_node

        fixed_code = ''
        safe_function_name = self.contract_usable_safe_function[repair_target_contract_name][safe_function_type]['safe_function_name']
        safe_contract_type = self.contract_usable_safe_function[repair_target_contract_name][safe_function_type]['safe_contract_type']

        if ast_node.nodeType == 'BinaryOperation':
            left_expression = ast_node.leftExpression.extract_code(self.contract_source_code, False)
            right_expression = ast_node.rightExpression.extract_code(self.contract_source_code, False)
            for replace_rule in replacement:
                left_expression = str(left_expression).replace(replace_rule['bug'], replace_rule['fixed'])
            for replace_rule in replacement:
                right_expression = str(right_expression).replace(replace_rule['bug'], replace_rule['fixed'])
            if safe_contract_type == 'library':
                if left_expression.isdigit():
                    left_expression = safe_function_type.split('@')[1] + '(' + left_expression + ')'
                fixed_code = '(' + left_expression + ').' + safe_function_name + '(' + right_expression + ')'
            else:
                fixed_code = safe_function_name + '(' + left_expression + ', ' + right_expression + ')'

        elif repair_target.ast_node.nodeType == 'UnaryOperation':
            left_expression = ast_node.subExpression.extract_code(self.contract_source_code, False)
            right_expression = '1'
            for replace_rule in replacement:
                left_expression = str(left_expression).replace(replace_rule['bug'], replace_rule['fixed'])
            if safe_contract_type == 'library':
                if left_expression.isdigit():
                    left_expression = safe_function_type.split('@')[1] + '(' + left_expression + ')'
                fixed_code = '(' + left_expression + ').' + safe_function_name + '(' + right_expression + ')'
            if safe_contract_type == 'contract':
                fixed_code = safe_function_name + '(' + left_expression + ', ' + right_expression + ')'

        elif repair_target.ast_node.nodeType == 'Assignment':
            left_expression = ast_node.leftHandSide.extract_code(self.contract_source_code, False)
            right_expression = ast_node.rightHandSide.extract_code(self.contract_source_code, False)
            for replace_rule in replacement:
                left_expression = str(left_expression).replace(replace_rule['bug'], replace_rule['fixed'])
            for replace_rule in replacement:
                right_expression = str(right_expression).replace(replace_rule['bug'], replace_rule['fixed'])
            if safe_contract_type == 'library':
                if left_expression.isdigit():
                    fixed_code = left_expression + ' = ' + safe_function_type.split('@')[1] + '(' + left_expression + ').' + safe_function_name + '(' + right_expression + ')'
                else:
                    fixed_code = left_expression + ' = ' + '(' + left_expression + ').' + safe_function_name + '(' + right_expression + ')'
            if safe_contract_type == 'contract':
                fixed_code = left_expression + ' = ' + safe_function_name + '(' + left_expression + ', ' + right_expression + ')'
        return fixed_code

    def will_cause_circular_inheritance(self, contract_a: Contract, contract_b: Contract) -> bool:

        all_contracts = {contract.name: contract for contract in self.slither.contracts}

        def has_inheritance_path(current_contract, target_contract_name, visited):
            if current_contract.name == target_contract_name:
                return True
            if current_contract.name in visited:
                return False
            visited.add(current_contract.name)
            for parent in current_contract.inheritance:
                if has_inheritance_path(parent, target_contract_name, visited):
                    return True
            for relation in self.additional_inherit_relation_ship:
                if relation.get(current_contract.name) == target_contract_name:
                    return True
                if current_contract.name in all_contracts:
                    parent_contract = all_contracts.get(relation.get(current_contract.name))
                    if parent_contract and has_inheritance_path(parent_contract, target_contract_name, visited):
                        return True
            return False

        if has_inheritance_path(contract_b, contract_a.name, set()):
            return True
        return False

    def get_additional_library_code(self):
        if len(self.additional_library_function_types) == 0:
            return ''
        additional_library_code = f'contract {self.additional_library_name} {{'
        for template_type in self.additional_library_function_types:
            operator = str(template_type).split('@')[0]
            operand_type = str(template_type).split('@')[1]
            if operator == '+':
                if operand_type in Uint:
                    additional_library_code += self.template.get_safe_add_uint_function_code(operand_type)
                elif operand_type in Int:
                    additional_library_code += self.template.get_safe_add_int_function_code(operand_type)
            elif operator == '-':
                if operand_type in Uint:
                    additional_library_code += self.template.get_safe_sub_uint_function_code(operand_type)
                elif operand_type in Int:
                    additional_library_code += self.template.get_safe_sub_int_function_code(operand_type)
            elif operator == '*':
                additional_library_code += self.template.get_safe_mul_function_code(operand_type)
            elif operator == '/':
                additional_library_code += self.template.get_safe_div_function_code(operand_type)
        additional_library_code += '\n}\n'
        return additional_library_code

    def get_modified_source_code(self):
        source_code = self.contract_source_code[:]

        def replace_string_in_line(original_string, line_number, old_substring, new_substring):
            lines = original_string.split('\n')
            if 0 < line_number <= len(lines):
                lines[line_number - 1] = lines[line_number - 1].replace(old_substring, new_substring)
                return '\n'.join(lines)
            else:
                return original_string

        for line in self.repair_targets_of_line:
            for replace_operation in self.replacements[line]:
                bug_code = replace_operation['bug']
                fixed_code = replace_operation['fixed']
                source_code = replace_string_in_line(source_code, line, bug_code, fixed_code)

        def replace_brace_in_multiline_string(string, start, end, replace_string):
            lines = string.split('\n')
            if start <= 0 or end > len(lines):
                return "Invalid start or end line number"
            for i in range(start - 1, end):
                line_ = lines[i]
                brace_index = line_.find('{')
                if brace_index != -1:
                    lines[i] = line_[:brace_index] + replace_string + line_[brace_index + 1:]
                    break
            return '\n'.join(lines)

        self.contract_source_node: Union[IterableNodeBase, NodeBase]
        for inherit_relation_ship in self.additional_inherit_relation_ship:
            inherit_relation_ship: {}
            for contract_node in self.source_root:
                if contract_node.nodeType == 'ContractDefinition' and contract_node.name in inherit_relation_ship:
                    line_numbers = contract_node.get_line_numbers(self.contract_source_code)
                    father_name = inherit_relation_ship[contract_node.name]
                    base_contracts = contract_node.baseContracts
                    need_replace = True
                    dest = ''
                    if len(base_contracts) != 0:
                        dest = ', ' + father_name + ' {'
                        for base_contract in base_contracts:
                            if str(base_contract.baseName.name) == father_name:
                                need_replace = False
                                break
                    else:
                        dest = 'is ' + father_name + ' {'
                    if need_replace:
                        source_code = replace_brace_in_multiline_string(source_code, line_numbers[0], line_numbers[1], dest)
                    break
        places_to_add_using_statement = []
        for using_relationship in self.additional_using_relation_ship:
            using_relationship: Dict
            for son_name, father_name_and_type in using_relationship.items():
                for contract_node in self.source_root:
                    if contract_node.nodeType == 'ContractDefinition' and contract_node.name == son_name:
                        line_numbers = contract_node.get_line_numbers(self.contract_source_code)
                        places_to_add_using_statement.append((line_numbers, father_name_and_type))
                        break

        places_to_add_using_statement = sorted(places_to_add_using_statement, key=lambda x: x[0][0], reverse=True)
        for place_to_add_tuple in places_to_add_using_statement:
            begin_line = place_to_add_tuple[0][0]
            end_line = place_to_add_tuple[0][1]
            father_name_and_type = place_to_add_tuple[1]
            father_name = str(father_name_and_type).split('@')[0]
            for_type = str(father_name_and_type).split('@')[1]
            statement = "{\n\tusing " + father_name + ' for ' + for_type + ';'
            source_code = replace_brace_in_multiline_string(source_code, begin_line, end_line, statement)

        return source_code
