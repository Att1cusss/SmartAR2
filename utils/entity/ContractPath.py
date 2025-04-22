from typing import List, Union, Optional
from slither.core.cfg.node import Node
from slither.core.declarations import Function
from slither.core.variables import Variable
from slither.slithir.operations import Operation
from z3 import And, Probe, BoolRef


class ContractPath:
    def __init__(self):
        self.path: List[Union[Operation, bool]] = []
        self.call_context_id: List[int] = []
        self.visited_ir_variables: List[Variable] = []
        self.state_variables = set()
        self.reference_of = {}
        self.constrains = []
        self.pc = -1
        self.alias_of = {}
        self.delta_of_collection = {}
        self.related_to_previous_value = {}
        self.revert = False
        self.return_value_receivers = []

    def deepcopy(self) -> "ContractPath":
        copy_path = ContractPath()
        copy_path.path = self.path[:]
        copy_path.call_context_id = self.call_context_id[:]
        copy_path.constrains = self.constrains[:]
        copy_path.visited_ir_variables = self.visited_ir_variables[:]
        copy_path.state_variables = self.state_variables.copy()
        copy_path.pc = self.pc
        copy_path.revert = self.revert
        return copy_path

    def register_alias(self, variable_name: str, alias: str):
        if variable_name is None or not isinstance(variable_name, str):
            return
        if self.get_context() not in self.alias_of:
            self.alias_of[self.get_context()] = {}
        if variable_name not in self.alias_of[self.get_context()]:
            self.alias_of[self.get_context()][variable_name] = []
        self.alias_of[self.get_context()][variable_name].append(alias)

    def get_first_alias_in_current_context(self, variable_name: str) -> Optional[str]:
        if self.get_context() in self.alias_of and variable_name in self.alias_of[self.get_context()] \
                and len(self.alias_of[self.get_context()][variable_name]) > 0:
            return self.alias_of[self.get_context()][variable_name][0]
        return None

    def get_latest_alias_in_current_context(self, variable_name: str) -> Optional[str]:
        if self.get_context() in self.alias_of and variable_name in self.alias_of[self.get_context()] \
                and len(self.alias_of[self.get_context()][variable_name]) > 0:
            return self.alias_of[self.get_context()][variable_name][-1]
        return None

    def register_delta_of_collection(self, collection: str, delta):
        if collection not in self.delta_of_collection:
            self.delta_of_collection[collection] = []
        self.delta_of_collection[collection].append(delta)

    def get_delta_of_collection(self, collection: str) -> List:
        if collection not in self.delta_of_collection:
            return []
        return self.delta_of_collection[collection]

    def append_path(self, contract_path: Optional["ContractPath"]):
        if contract_path is None:
            return
        self.path.extend(contract_path.path)
        self.call_context_id.extend(contract_path.call_context_id)

    def append_ir(self, ir: Operation, call_context_id: int):
        self.path.append(ir)
        self.call_context_id.append(call_context_id)
        for v in ir.node.state_variables_read:
            self.state_variables.add(v.name)
        for v in ir.node.state_variables_written:
            self.state_variables.add(v.name)

    def pop_ir(self):
        self.path.pop()

    def is_finished(self) -> bool:
        return self.pc == len(self.path) - 1

    def get_next_ir(self) -> Operation:
        self.pc += 1
        ir = self.path[self.pc]
        return ir

    def get_current_ir(self):
        return self.path[self.pc]

    def get_current_node(self) -> Node:
        return self.get_current_ir().node

    def get_next_node(self) -> Node:
        current_node = self.get_current_node()
        i = self.pc + 1
        while i < len(self.path):
            if self.path[i].node != current_node:
                return self.path[i].node
            i += 1
        return current_node

    def get_current_function(self) -> Function:
        return self.get_current_ir().node.function

    def get_context(self) -> int:
        return self.call_context_id[self.pc]

    def get_next_context(self) -> int:
        current_context_id = self.call_context_id[self.pc]
        i = self.pc + 1
        while i < len(self.call_context_id):
            if self.call_context_id[i] != current_context_id:
                return self.call_context_id[i]
            i += 1
        return current_context_id

    def get_base_context(self) -> int:
        return self.call_context_id[0]

    def add_path_constrain(self, constrain):
        if isinstance(constrain, List) and len(constrain) == 0:
            return
        if isinstance(constrain, List):
            self.constrains.extend(constrain)
        else:
            self.constrains.append(constrain)

    def visit_variable(self, var: Variable):
        self.visited_ir_variables.append(var)

    def print_path_constrain(self):
        print(self.constrains)

    def get_path_constrain(self) -> Optional[Union[Probe, BoolRef]]:
        if self.revert or len(self.constrains) == 0:
            return None
        return And(self.constrains)

    def set_revert(self, revert: bool):
        self.revert = revert

    def is_revert(self) -> bool:
        return self.revert

    def register_return_value_receiver(self, receiver: str):
        self.return_value_receivers.append(receiver)

    def get_return_value_receiver(self):
        return self.return_value_receivers.pop()

    def get_path_length(self):
        return len(self.path)

    def has_write_state_variable(self, state_variable_name: str) -> bool:
        for ir in self.path:
            if isinstance(ir, Operation):
                if ir.node is not None and ir.node.state_variables_written is not None and \
                        len(ir.node.state_variables_written) > 0:
                    written_state_variables = [var.name for var in ir.node.state_variables_written]
                    if state_variable_name in written_state_variables:
                        return True
        return False

    def to_string(self):
        string = ''
        for i in range(len(self.path)):
            string += f'{self.call_context_id[i]}:{self.path[i].node.function}.{self.path[i].node.node_id}:{self.path[i]}'
            if i != len(self.path) - 1:
                string += ' --> '
        return string

    def to_string_simplified(self):
        string = ''
        for i in range(len(self.path)):
            string += f'{self.call_context_id[i]}:{self.path[i].node.function}.{self.path[i].node.node_id}'
            if i != len(self.path) - 1:
                string += ' --> '
        return string
