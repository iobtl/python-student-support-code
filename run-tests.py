import os

import compiler_register_allocator as compiler

# import compiler
import interp_Cif
import interp_Lwhile
import type_check_Lwhile
from utils import run_tests, run_one_test
from interp_x86.eval_x86 import interp_x86

compiler = compiler.Compiler()

typecheck_Lwhile = type_check_Lwhile.TypeCheckLwhile().type_check

typecheck_dict = {
    "source": typecheck_Lwhile,
    "shrink": typecheck_Lwhile,
    "remove_complex_operands": typecheck_Lwhile,
}

interpCif = interp_Cif.InterpCif().interp
interpLwhile = interp_Lwhile.InterpLwhile().interp
interp_dict = {
    "shrink": interpLwhile,
    "remove_complex_operands": interpLwhile,
    "explicate_control": interpCif,
    "select_instructions": interp_x86,
    "remove_jumps": interp_x86,
    "assign_homes": interp_x86,
    "patch_instructions": interp_x86,
}

TESTNAME = os.getenv("TESTNAME", "")

if TESTNAME:
    run_one_test(
        os.getcwd() + f"/tests/var/{TESTNAME}.py",
        "var",
        compiler,
        "var",
        typecheck_dict,
        interp_dict,
    )
else:
    run_tests("var", compiler, "var", typecheck_dict, interp_dict)
