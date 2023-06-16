import os

import compiler_register_allocator as compiler

# import compiler
import interp_Ctup
import interp_Lfun
import type_check_Lfun
import type_check_Ctup
from utils import run_tests, run_one_test
from interp_x86.eval_x86 import interp_x86

compiler = compiler.Compiler()

typecheck_Lfun = type_check_Lfun.TypeCheckLfun().type_check
typecheck_Ctup = type_check_Ctup.TypeCheckCtup().type_check

typecheck_dict = {
    "source": typecheck_Lfun,
    "shrink": typecheck_Lfun,
    "expose_allocation": typecheck_Lfun,
    "remove_complex_operands": typecheck_Lfun,
    "explicate_control": typecheck_Ctup,
}

interpCtup = interp_Ctup.InterpCtup().interp
interpLfun = interp_Lfun.InterpLfun().interp

interp_dict = {
    "shrink": interpLfun,
    "reveal_functions": interpLfun,
    # "limit_functions": interpLfun,
    "expose_allocation": interpLfun,
    "remove_complex_operands": interpLfun,
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
