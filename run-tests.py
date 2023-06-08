import os

import compiler_register_allocator as compiler

# import compiler
import interp_Ctup
import interp_Ltup
import type_check_Ltup
from utils import run_tests, run_one_test
from interp_x86.eval_x86 import interp_x86

compiler = compiler.Compiler()

typecheck_Ltup = type_check_Ltup.TypeCheckLtup().type_check

typecheck_dict = {
    "source": typecheck_Ltup,
    "shrink": typecheck_Ltup,
    "expose_allocation": typecheck_Ltup,
    "remove_complex_operands": typecheck_Ltup,
}

interpCtup = interp_Ctup.InterpCtup().interp
interpLtup = interp_Ltup.InterpLtup().interp

interp_dict = {
    "shrink": interpLtup,
    "expose_allocation": interpLtup,
    "remove_complex_operands": interpLtup,
    "explicate_control": interpCtup,
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
