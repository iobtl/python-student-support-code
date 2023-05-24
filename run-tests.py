import os

import compiler_register_allocator as compiler

# import compiler
import interp_Lif
import type_check_Lvar
import type_check_Lif
from utils import run_tests, run_one_test
from interp_x86.eval_x86 import interp_x86

compiler = compiler.Compiler()

typecheck_Lvar = type_check_Lvar.TypeCheckLvar().type_check
typecheck_Lif = type_check_Lif.TypeCheckLif().type_check

typecheck_dict = {
    "source": typecheck_Lif,
    "shrink": typecheck_Lif,
    "remove_complex_operands": typecheck_Lvar,
}
interpLif = interp_Lif.InterpLif().interp
interp_dict = {
    "shrink": interpLif,
    "remove_complex_operands": interpLif,
    "select_instructions": interp_x86,
    "assign_homes": interp_x86,
    "patch_instructions": interp_x86,
}

if False:
    run_one_test(
        os.getcwd() + "/tests/var/zero.py",
        "var",
        compiler,
        "var",
        typecheck_dict,
        interp_dict,
    )
else:
    run_tests("var", compiler, "var", typecheck_dict, interp_dict)
