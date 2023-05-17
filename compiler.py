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
                (v_exp, v_temp) = self.rco_exp(v, need_atomic)

                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*v_temp, (tmp, UnaryOp(USub(), v_exp))])
                else:
                    return (UnaryOp(USub(), v_exp), v_temp)
            case BinOp(a, Add(), b):
                (a_exp, a_temp) = self.rco_exp(a, need_atomic)
                (b_exp, b_temp) = self.rco_exp(b, need_atomic)

                # Turn result of binary op into another temporary
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*a_temp, *b_temp, (tmp, BinOp(a_exp, Add(), b_exp))])
                else:
                    return (BinOp(a_exp, Add(), b_exp), [*a_temp, *b_temp])
            case BinOp(a, Sub(), b):
                (a_exp, a_temp) = self.rco_exp(a, need_atomic)
                (b_exp, b_temp) = self.rco_exp(b, need_atomic)

                # Turn result of binary op into another temporary
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*a_temp, *b_temp, (tmp, BinOp(a_exp, Sub(), b_exp))])
                else:
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
                (e, e_temp) = self.rco_exp(exp, False)
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
        match p:
            case Module(body):
                return Module([s for stmt in body for s in self.rco_stmt(stmt)])
            case _:
                pass

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        match e:
            case Constant(c):
                return Immediate(c)
            case Name(n):
                return Variable(n)
            case _:
                raise Exception("Unsupported atomic expression: ", e)

    def select_stmt(self, s: stmt) -> list[instr]:
        match s:
            case Expr(Call(Name("print"), [atm])):
                return [
                    Instr("movq", [self.select_arg(atm), Reg("rdi")]),
                    Callq(label_name("print_int"), 1),
                ]
            case Expr(exp):
                match exp:
                    case Call(Name("input_int"), []):
                        return [Callq(label_name("read_int"), 0)]
                    case UnaryOp(USub(), atm):
                        return [Instr("negq", [self.select_arg(atm)])]
                    case BinOp(a, op, b):
                        if str(op) == "+":
                            op_instr = "addq"
                        elif str(op) == "-":
                            op_instr = "subq"
                        else:
                            raise Exception("Unsupported binary op in assign: ", s)

                        a_arg, b_arg = self.select_arg(a), self.select_arg(b)
                        return [
                            Instr("movq", [a_arg, Reg("rax")]),
                            Instr(op_instr, [b_arg, Reg("rax")]),
                        ]
                    case e:
                        return [Instr("movq", [self.select_arg(e), Reg("rax")])]
            case Assign([Name(var)], BinOp(atm_a, op, atm_b)) if str(
                atm_a
            ) == var or str(atm_b) == var:
                # Handle special case  when `a` or `b` is `var`
                if str(op) == "+":
                    op_instr = "addq"
                elif str(op) == "-":
                    op_instr = "subq"
                else:
                    raise Exception("Unsupported binary op in assign: ", s)

                a_arg, b_arg = self.select_arg(atm_a), self.select_arg(atm_b)
                if str(a_arg) == var:
                    return [Instr(op_instr, [b_arg, Variable(var)])]
                else:
                    return [Instr(op_instr, [a_arg, Variable(var)])]
            case Assign([Name(var)], UnaryOp(USub(), atm)):
                return [
                    Instr("movq", [self.select_arg(atm), Variable(var)]),
                    Instr("negq", [Variable(var)]),
                ]
            case Assign([Name(var)], expr):
                expr_instr = self.select_stmt(Expr(expr))
                return [*expr_instr, Instr("movq", [Reg("rax"), Variable(var)])]

    def select_instructions(self, p: Module) -> X86Program:
        match p:
            case Module(body):
                return X86Program(
                    [instr for stmt in body for instr in self.select_stmt(stmt)]
                )
            case _:
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
