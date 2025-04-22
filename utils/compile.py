import json
import os
import shutil
import subprocess
import time
import solcx
from py_solidity_parser.main import from_ast
from slither import Slither
from PathConfig import IO_DIR, CONTRACTS_DIR


def execute_cmd_with_timeout(cmd, timeout=300):
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    t_beginning = time.time()
    while True:
        seconds_passed = time.time() - t_beginning
        if p.poll() is not None:
            return str(round(float(seconds_passed), 2))
        if seconds_passed > timeout:
            p.terminate()
            return 'timeout, seconds_passed:' + str(timeout)
        time.sleep(0.1)


def change_solc_version_to(_version):
    cmd = 'solc-select use ' + _version
    os.system(cmd)


def read_source_code(contract_path=os.path.join(CONTRACTS_DIR, 'sample.sol')) -> str:
    with open(contract_path, 'r', encoding='utf8') as fp:
        contract_source_code = fp.read()
    fp.close()
    return contract_source_code


def compile_contract(contract_path=os.path.join(CONTRACTS_DIR, 'sample.sol')) -> dict:
    standard_json_path = os.path.join(IO_DIR, 'input.json')
    compile_input_json = json.load(open(standard_json_path))
    compile_input_json["sources"]["destructible"]["content"] = read_source_code(contract_path)
    compile_output_json = solcx.compile_standard(compile_input_json)
    return compile_output_json


def build_ast(compile_output_json: dict) -> dict:
    assert compile_output_json is not None
    return from_ast(compile_output_json["sources"]["destructible"]["ast"])


def build_slither(contract_path=os.path.join(CONTRACTS_DIR, 'sample.sol')) -> Slither:
    return Slither(contract_path, disable_solc_warnings=True)


def copy_file(src, dest):
    if os.path.exists(src):
        shutil.copy(src, dest)
        print(f"Copied: {src} -> {dest}")
    else:
        print(f"Source file not found: {src}")


