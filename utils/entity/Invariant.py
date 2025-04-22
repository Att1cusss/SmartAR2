import re


class Invariant:
    def __init__(self, left: str, left_type: str, op: str, right: str, right_type: str):
        assert left_type in ['variable', 'constant', 'collection']
        assert right_type in ['variable', 'constant', 'collection']
        assert op in ['>', '>=', '==', '<=', '<']
        self.left = left
        self.left_type = left_type
        self.op = op
        self.right = right
        self.right_type = right_type

    def to_string(self):
        return f'{self.left}({self.left_type}) {self.op} {self.right}({self.right_type})'

    @staticmethod
    def from_string(invariant_str: str):
        pattern = r'(\w+)\((\w+)\) (>|>=|==|<=|<) (\w+)\((\w+)\)'
        match = re.match(pattern, invariant_str)
        if match:
            left, left_type, op, right, right_type = match.groups()
            return Invariant(left, left_type, op, right, right_type)
        else:
            raise ValueError(f"Invalid invariant string format: {invariant_str}")
