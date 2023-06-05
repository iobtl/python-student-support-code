import os

import compiler_register_allocator as compiler

# import compiler
import interp_Cif
import interp_Lif
import type_check_Lvar
import type_check_Lif
from utils import run_tests, run_one_test
from interp_x86.eval_x86 import interp_x86

compiler = compiler.Compiler()

typecheck_Lif = type_check_Lif.TypeCheckLif().type_check

typecheck_dict = {
    "source": typecheck_Lif,
    "shrink": typecheck_Lif,
    "remove_complex_operands": typecheck_Lif,
}
interpLif = interp_Lif.InterpLif().interp
interpCif = interp_Cif.InterpCif().interp
interp_dict = {
    "shrink": interpLif,
    "remove_complex_operands": interpLif,
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
