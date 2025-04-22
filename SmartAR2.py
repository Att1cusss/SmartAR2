import os.path
import argparse
from collections import defaultdict
from typing import List, Set, Dict

from PathConfig import CONTRACTS_DIR
from patcher.PatchGenerator2 import PatchGenerator2
from patcher.safe_math_finder import SafeMathFinderSMT
from recognizer.fp.FalsePositiveRecognizer import FalsePositiveRecognizer
from recognizer.target.RedundantTargetReducer import RedundantTargetReducer
from utils.compile import change_solc_version_to, read_source_code, build_ast, compile_contract, build_slither
from utils.entity.RepairTarget import RepairTarget
from utils.locate import locate_repair_targets


class SmartAR2:
    def __init__(self, compiler_version: str, bug_lines: List[int], fp=True, redundant=True, reuse=True):
        self.bug_lines = bug_lines
        self.repair_targets = []
        self.fp_targets = None
        self.tp_targets = []
        self.minimum_repair_targets = []
        change_solc_version_to(compiler_version)
        self.source_code = read_source_code()
        self.source_root = build_ast(compile_output_json=compile_contract())
        self.slither = build_slither()
        self.filter_false_positive = fp
        self.reduce_redundant = redundant
        self.reuse_safemath = reuse
        self.reusable_safemath_functions = defaultdict(list)

    def process(self):
        # Step 1: Locate repair targets
        print(f'[+] Locating repair targets...')
        if len(self.bug_lines) == 0:
            print('[+] No bug lines provided.')
            return
        else:
            for bug_line in self.bug_lines:
                try:
                    self.repair_targets.extend(
                        locate_repair_targets(self.source_root, self.slither, self.source_code, bug_line)
                    )
                except Exception as e:
                    continue

        self.repair_targets: List[RepairTarget]
        if len(self.repair_targets) == 0:
            print('[+] No repair targets found.')
            return
        print(f'[+] Located {len(self.repair_targets)} repair targets.')

        # Step 2: Filter false positives
        if self.filter_false_positive:
            print('[+] Filtering false positive repair targets...')
            try:
                fp_recognizer = FalsePositiveRecognizer(repair_targets=self.repair_targets)
                self.tp_targets, self.fp_targets = fp_recognizer.recognize_true_positive()
                self.tp_targets: Set[RepairTarget]
                self.fp_targets: Dict[RepairTarget, str]  # {fp: reason}
            except Exception as e:
                pass
            print(f'[+] Filtered {len(self.fp_targets)} false positives, {len(self.tp_targets)} targets remaining.')
            if len(self.tp_targets) == 0:
                print('[+] No repair targets left after filtering.')
                return
        else:
            self.tp_targets = self.repair_targets

        # Step 3: Reduce redundant repair targets
        if self.reduce_redundant:
            print('[+] Reducing redundant repair targets...')
            try:
                reducer = RedundantTargetReducer(slither=self.slither, repair_targets=list(self.tp_targets))
                self.minimum_repair_targets = reducer.reduce_redundant_repair_targets()
            except Exception as e:
                pass
            print(f'[+] Reduced {len(self.tp_targets) - len(self.minimum_repair_targets)} redundant targets, '
                  f'{len(self.minimum_repair_targets)} remaining.')
            if len(self.minimum_repair_targets) == 0:
                print('[+] No repair targets left after reduction.')
                return
        else:
            self.minimum_repair_targets = self.tp_targets

        # Step 4: Find reusable safe math functions
        if self.reuse_safemath:
            print('[+] Finding reusable SafeMath functions...')
            try:
                safemath_finder = SafeMathFinderSMT(self.slither)
                candidates = safemath_finder.structural_judgement()
                for function in candidates:
                    is_safemath_function, function_type = safemath_finder.functional_judgement(function)
                    if is_safemath_function:
                        self.reusable_safemath_functions[function_type].append(function)
            except Exception as e:
                pass
            print(f'[+] Identified {len(self.reusable_safemath_functions)} SafeMath functions.')

        # Step 5: Generate patch
        print('[+] Generating patch code...')
        try:
            patch_generator = PatchGenerator2(
                repair_targets=self.minimum_repair_targets,
                contract_source_code=self.source_code,
                slither=self.slither,
                source_root=self.source_root,
                reusable_safemath_functions=self.reusable_safemath_functions
            )
            patch_generator.process()
        except Exception as e:
            print(f"[ERROR] Error occurred during patch generation: {e}")
            return
        print(f'[+] Patch generated successfully at: {os.path.join(CONTRACTS_DIR, "fixed.sol")}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Run SmartAR2 with specified compiler version and bug lines.')
    parser.add_argument('--version', type=str, required=True, help='Solidity compiler version (e.g., 0.4.26)')
    parser.add_argument('--lines', type=str, required=True, help='Comma-separated list of bug lines (e.g., 10,12,13)')

    args = parser.parse_args()
    bug_lines_list = sorted([int(x.strip()) for x in args.lines.split(',')])

    smart_ar = SmartAR2(
        compiler_version=args.version,
        bug_lines=bug_lines_list,
        fp=True,
        redundant=True,
        reuse=True
    )
    smart_ar.process()
