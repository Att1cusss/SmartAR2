from slither import Slither
from slither.core.cfg.node import Node
from slither.core.declarations import FunctionContract
from slither.core.solidity_types.elementary_type import Int
from slither.slithir.operations import Binary


class RepairTarget:
    def __init__(self, source_code: str, slither: Slither, slither_function_node: FunctionContract,
                 slither_statement_node: Node, ir: Binary, ast_root, ast_node):
        self.source_code = source_code
        self.slither = slither
        self.slither_function_node = slither_function_node
        self.slither_statement_node = slither_statement_node
        self.ir = ir
        self.ast_root = ast_root
        self.ast_node = ast_node

    def print_info(self):
        print(self.to_string())

    def to_string_(self):
        info = '[RepairTarget] '
        info += self.slither_function_node.contract.name + ':' + self.slither_function_node.name + ':'
        info += str(self.ast_node.extract_code(self.source_code, True).split(": ")[0]) + '\n'
        info += 'CODE: ' + self.slither_statement_node.source_mapping.content + '\n'
        info += 'OPERATION: '

        if self.ast_node.nodeType == 'BinaryOperation':
            info += self.ast_node.leftExpression.extract_code(self.source_code, False) + ' '
            info += '[' + self.ast_node.operator + '] '
            info += self.ast_node.rightExpression.extract_code(self.source_code, False) + '\n'
        elif self.ast_node.nodeType == 'UnaryOperation':
            info += '[' + self.ast_node.operator + '] '
            info += self.ast_node.subExpression.extract_code(self.source_code, False) + '\n'
        elif self.ast_node.nodeType == 'Assignment':
            info += self.ast_node.leftHandSide.extract_code(self.source_code, False) + ' '
            info += '[' + self.ast_node.operator + '] '
            info += self.ast_node.rightHandSide.extract_code(self.source_code, False) + '\n'

        info += 'SSA: '
        if self.ast_node.nodeType in ['BinaryOperation', 'UnaryOperation', 'Assignment']:
            info += str(self.ir.variable_left) + ' [' + self.ir.type_str + '] ' + str(self.ir.variable_right)
            info += ' --> ' + str(self.ir.lvalue) + '\n'

        return info

    def get_line_number(self) -> int:
        return int(self.ast_node.extract_code(self.source_code, True).split(": ")[0])

    def to_string(self) -> str:
        info = '[RepairTarget] '
        info += self.slither_function_node.contract.name + ':' + self.slither_function_node.name + ':'
        info += str(self.ast_node.extract_code(self.source_code, True).split(": ")[0]) + '\n'

        info += 'loc(src): '
        if self.ast_node.nodeType == 'BinaryOperation':
            info += self.ast_node.leftExpression.extract_code(self.source_code, False) + ' '
            info += '[' + self.ast_node.operator + '] '
            info += self.ast_node.rightExpression.extract_code(self.source_code, False) + '\n'
        elif self.ast_node.nodeType == 'UnaryOperation':
            info += '[' + self.ast_node.operator + '] '
            info += self.ast_node.subExpression.extract_code(self.source_code, False) + '\n'
        elif self.ast_node.nodeType == 'Assignment':
            info += self.ast_node.leftHandSide.extract_code(self.source_code, False) + ' '
            info += '[' + self.ast_node.operator + '] '
            info += self.ast_node.rightHandSide.extract_code(self.source_code, False) + '\n'

        info += 'loc(SSA): '
        if self.ast_node.nodeType in ['BinaryOperation', 'UnaryOperation', 'Assignment']:
            info += str(self.ir.lvalue) + ' = '
            info += str(self.ir.variable_left) + ' [' + self.ir.type_str + '] ' + str(self.ir.variable_right)
            info += '\n'

        info += 'type: '
        cond = '...'
        if self.ir.type_str in ['+']:
            if self.ir.variable_left.type in Int:
                info += 'signed ADD' + '\n'
                cond = '...'
            else:
                info += 'unsigned ADD' + '\n'
                cond = str(self.ir.variable_left.name) + ' ' + self.ir.type_str + ' ' + str(self.ir.variable_right.name)
                cond += f' < {str(self.ir.variable_left.name)}'
        elif self.ir.type_str in ['*']:
            if self.ir.variable_left.type in Int:
                info += 'signed MUL' + '\n'
                cond = '...'
            else:
                info += 'unsigned MUL' + '\n'
                cond = '...'
        elif self.ir.type_str in ['-']:
            if self.ir.variable_left.type in Int:
                info += 'signed SUB' + '\n'
                cond = '...'
            else:
                info += 'unsigned SUB' + '\n'
                cond = '...'
        elif self.ir.type_str in ['/']:
            if self.ir.variable_left.type in Int:
                info += 'signed DIV' + '\n'
                cond = '...'
            else:
                info += 'unsigned DIV' + '\n'
                cond = '...'

        info += f'cond: {cond}'

        return info
