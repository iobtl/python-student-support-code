import ast
import os

from ast import *
from typing import Set

from utils import *
from x86_ast import *

Binding = tuple[Name, expr]
Temporaries = list[Binding]


class Compiler:
    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr, Temporaries]:
        match e:
            case Constant(_) | Name(_):
                return (e, [])
            case Call(Name("input_int"), []):
                i = Name(generate_name("input"))
                return (i, [(i, Call(Name("input_int"), []))])
            case UnaryOp(USub(), v):
                tmp = Name(generate_name("tmp"))
                (v_exp, v_temp) = self.rco_exp(v, True)

                return (tmp, [*v_temp, (tmp, v_exp)])
            case BinOp(a, Add(), b):
                (a_exp, a_temp) = self.rco_exp(a, True)
                (b_exp, b_temp) = self.rco_exp(b, True)

                return (BinOp(a_exp, Add(), b_exp), [*a_temp, *b_temp])
            case BinOp(a, Sub(), b):
                (a_exp, a_temp) = self.rco_exp(a, True)
                (b_exp, b_temp) = self.rco_exp(b, True)

                return (BinOp(a_exp, Sub(), b_exp), [*a_temp, *b_temp])
            case _:
                raise Exception("Unsupported expression: ", e)

    def rco_stmt(self, s: stmt) -> list[stmt]:
        match s:
            case Expr(Call(Name("print"), [exp])):
                (e, e_temp) = self.rco_exp(exp, True)
                stmts = [Assign([name], value) for name, value in e_temp]
                stmts.append(Expr(Call(Name("print"), [e])))

                return stmts
            case Expr(exp):
                (e, e_temp) = self.rco_exp(exp, True)
                stmts = [Assign([name], value) for name, value in e_temp]
                stmts.append(Expr(e))

                return stmts
            case Assign([Name(var)], exp):
                (e, e_temp) = self.rco_exp(exp, True)
                stmts = [Assign([name], value) for name, value in e_temp]
                stmts.append(Assign([Name(var)], e))

                return stmts
            case _:
                raise Exception("Unsupported statement: ", s)

    def remove_complex_operands(self, p: Module) -> Module:
        """Converts all complex expressions into atomic expressions.

        Pass: L_{Var} -> L_{Var}^{mon}
        """
        print(p)
        match p:
            case Module(body):
                return Module([s for stmt in body for s in self.rco_stmt(stmt)])
            case _:
                pass

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        pass

    def select_stmt(self, s: stmt) -> list[instr]:
        # YOUR CODE HERE
        pass

    def select_instructions(self, p: Module) -> X86Program:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        pass

    def assign_homes_instr(self, i: instr, home: dict[Variable, arg]) -> instr:
        # YOUR CODE HERE
        pass

    def assign_homes_instrs(
        self, ss: list[instr], home: dict[Variable, arg]
    ) -> list[instr]:
        # YOUR CODE HERE
        pass

    def assign_homes(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        # YOUR CODE HERE
        pass

    def patch_instrs(self, ss: list[instr]) -> list[instr]:
        # YOUR CODE HERE
        pass

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass
