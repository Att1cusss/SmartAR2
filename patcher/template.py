import os

from PathConfig import PATCHER_DIR


class Template:
    def __init__(self):
        self.add_uint_template = os.path.join(PATCHER_DIR, 'template/add_uint.txt')
        self.add_int_template = os.path.join(PATCHER_DIR, 'template/add_int.txt')
        self.sub_uint_template = os.path.join(PATCHER_DIR, 'template/sub_uint.txt')
        self.sub_int_template = os.path.join(PATCHER_DIR, 'template/sub_int.txt')
        self.mul_template = os.path.join(PATCHER_DIR, 'template/mul.txt')
        self.div_template = os.path.join(PATCHER_DIR, 'template/div.txt')

    def get_safe_add_uint_function_code(self, l_type: str, r_type=None, return_type=None) -> str:
        if r_type is None:
            r_type = l_type
        if return_type is None:
            return_type = l_type
        with open(self.add_uint_template, 'r', encoding='utf-8') as file:
            template_code = file.read()
        file.close()
        return template_code.replace('$return_type$', return_type).replace('$l_type$', l_type).replace('$r_type$', r_type)

    def get_safe_add_int_function_code(self, l_type: str, r_type=None, return_type=None) -> str:
        if r_type is None:
            r_type = l_type
        if return_type is None:
            return_type = l_type
        with open(self.add_int_template, 'r', encoding='utf-8') as file:
            template_code = file.read()
        file.close()
        return template_code.replace('$return_type$', return_type).replace('$l_type$', l_type).replace('$r_type$', r_type)

    def get_safe_sub_uint_function_code(self, l_type: str, r_type=None, return_type=None) -> str:
        if r_type is None:
            r_type = l_type
        if return_type is None:
            return_type = l_type
        with open(self.sub_uint_template, 'r', encoding='utf-8') as file:
            template_code = file.read()
        file.close()
        return template_code.replace('$return_type$', return_type).replace('$l_type$', l_type).replace('$r_type$', r_type)

    def get_safe_sub_int_function_code(self, l_type: str, r_type=None, return_type=None) -> str:
        if r_type is None:
            r_type = l_type
        if return_type is None:
            return_type = l_type
        with open(self.sub_int_template, 'r', encoding='utf-8') as file:
            template_code = file.read()
        file.close()
        return template_code.replace('$return_type$', return_type).replace('$l_type$', l_type).replace('$r_type$', r_type)

    def get_safe_mul_function_code(self, l_type: str, r_type=None, return_type=None) -> str:
        if r_type is None:
            r_type = l_type
        if return_type is None:
            return_type = l_type
        with open(self.mul_template, 'r', encoding='utf-8') as file:
            template_code = file.read()
        file.close()
        return template_code.replace('$return_type$', return_type).replace('$l_type$', l_type).replace('$r_type$', r_type)

    def get_safe_div_function_code(self, l_type: str, r_type=None, return_type=None) -> str:
        if r_type is None:
            r_type = l_type
        if return_type is None:
            return_type = l_type
        with open(self.div_template, 'r', encoding='utf-8') as file:
            template_code = file.read()
        file.close()
        return template_code.replace('$return_type$', return_type).replace('$l_type$', l_type).replace('$r_type$', r_type)
