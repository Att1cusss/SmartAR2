from typing import Optional

from slither.core.cfg.node import Node
from slither.slithir.operations import Condition, Binary, SolidityCall


class TreeNode:
    def __init__(self, variable=None, op=None, left=None, right=None):
        self.variable = variable
        self.op = op
        self.left = left
        self.right = right


def build_if_expression_tree(if_node: Node) -> Optional[TreeNode]:
    assert len(if_node.irs_ssa) >= 1
    assert isinstance(if_node.irs_ssa[-1], Condition)
    condition_ir = if_node.irs_ssa[-1]
    condition_ir: Condition
    root = None
    for ir in if_node.irs_ssa:
        if isinstance(ir, Binary) and ir.lvalue.name == condition_ir.value.name:
            root = build_expression_tree(condition_ir.value, if_node)
            return root
    return root


def build_binary_expression_tree(ir: Binary, node: Node) -> Optional[TreeNode]:
    root = build_expression_tree(ir.lvalue, node)
    return root


def build_require_assert_expression_tree(node: Node) -> Optional[TreeNode]:
    assert len(node.irs_ssa) >= 1
    assert isinstance(node.irs_ssa[-1], SolidityCall)
    call_ir = node.irs_ssa[-1]
    call_ir: SolidityCall
    call_arg = call_ir.arguments[0]
    for arg in call_ir.arguments:
        if str(arg.type) == 'bool':
            call_arg = arg
            break
    root = build_expression_tree(call_arg, node)
    return root


def build_expression_tree(variable, node: Node, level=0) -> TreeNode:
    root = TreeNode(variable=variable)
    if level > 10:
        return root
    for ir in node.irs_ssa:
        if isinstance(ir, Binary) and ir.lvalue.name == variable.name:
            root.op = ir.type_str
            root.left = build_expression_tree(ir.variable_left, node, level + 1)
            root.right = build_expression_tree(ir.variable_right, node, level + 1)
            return root
    return root


def print_tree(node, level=0, prefix="Root: "):
    if node is not None:
        indent = "    " * level
        print(f"{indent}{prefix}Variable: {node.variable}, Operation: {node.op}")
        if node.left:
            print_tree(node.left, level + 1, prefix="L--- ")
        if node.right:
            print_tree(node.right, level + 1, prefix="R--- ")


def get_leaf_nodes(node):
    if node is None:
        return []
    if node.left is None and node.right is None:
        return [node]
    leaves = []
    if node.left:
        leaves.extend(get_leaf_nodes(node.left))
    if node.right:
        leaves.extend(get_leaf_nodes(node.right))
    return leaves
