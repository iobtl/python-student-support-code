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
    # Shrink
    ############################################################################

    def shrink(self, p: Module) -> Module:
        def _shrink_exp(e: expr) -> expr:
            match e:
                case BoolOp(And(), [e1, e2]):
                    # e2 if e1 else False
                    return IfExp(_shrink_exp(e1), _shrink_exp(e2), Constant(False))
                case BoolOp(Or(), [e1, e2]):
                    # True if e1 else e2
                    return IfExp(_shrink_exp(e1), Constant(True), _shrink_exp(e2))
                case BinOp(e1, op, e2):
                    return BinOp(_shrink_exp(e1), op, _shrink_exp(e2))
                case UnaryOp(op, e):
                    return UnaryOp(op, _shrink_exp(e))
                case Compare(e1, [cmp], [e2]):
                    return Compare(_shrink_exp(e1), [cmp], [_shrink_exp(e2)])
                case IfExp(e, s1, s2):
                    return IfExp(_shrink_exp(e), s1, s2)
                case _:
                    return e

        def _shrink_stmt(s: stmt) -> stmt:
            match s:
                case If(e, s1, s2):
                    return If(
                        _shrink_exp(e),
                        [_shrink_stmt(s) for s in s1],
                        [_shrink_stmt(s) for s in s2],
                    )
                case Assign(name, e):
                    return Assign(name, _shrink_exp(e))
                case Expr(e):
                    return Expr(_shrink_exp(e))
                case _:
                    return s

        return Module([_shrink_stmt(s) for s in p.body])

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
            case Compare(a, [cmp], [b]):
                (a_exp, a_temp) = self.rco_exp(a, True)
                (b_exp, b_temp) = self.rco_exp(b, True)

                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (
                        tmp,
                        [*a_temp, *b_temp, (tmp, Compare(a_exp, [cmp], [b_exp]))],
                    )
                else:
                    return (Compare(a_exp, [cmp], [b_exp]), [*a_temp, *b_temp])
            case UnaryOp(USub(), v):
                (v_exp, v_temp) = self.rco_exp(v, True)

                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*v_temp, (tmp, UnaryOp(USub(), v_exp))])
                else:
                    return (UnaryOp(USub(), v_exp), v_temp)
            case UnaryOp(Not(), v):
                (v_exp, v_temp) = self.rco_exp(v, False)

                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*v_temp, (tmp, UnaryOp(Not(), v_exp))])
                else:
                    return (UnaryOp(Not(), v_exp), v_temp)
            case BinOp(a, Add(), b):
                (a_exp, a_temp) = self.rco_exp(a, True)
                (b_exp, b_temp) = self.rco_exp(b, True)

                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*a_temp, *b_temp, (tmp, BinOp(a_exp, Add(), b_exp))])
                else:
                    return (BinOp(a_exp, Add(), b_exp), [*a_temp, *b_temp])
            case BinOp(a, Sub(), b):
                (a_exp, a_temp) = self.rco_exp(a, True)
                (b_exp, b_temp) = self.rco_exp(b, True)

                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*a_temp, *b_temp, (tmp, BinOp(a_exp, Sub(), b_exp))])
                else:
                    return (BinOp(a_exp, Sub(), b_exp), [*a_temp, *b_temp])
            case IfExp(cond, e1, e2):
                (cond_exp, cond_temp) = self.rco_exp(cond, False)
                (e1_exp, e1_temp) = self.rco_exp(e1, True)
                (e2_exp, e2_temp) = self.rco_exp(e2, True)

                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (
                        tmp,
                        [
                            *cond_temp,
                            *e1_temp,
                            *e2_temp,
                            (tmp, IfExp(cond_exp, e1_exp, e2_exp)),
                        ],
                    )
                else:
                    return (
                        IfExp(cond_exp, e1_exp, e2_exp),
                        [*cond_temp, *e1_temp, *e2_temp],
                    )
            case Begin(stmts, e):
                (e_exp, e_temp) = self.rco_exp(e, False)

                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*e_temp, (tmp, Begin(stmts, e_exp))])
                else:
                    # TODO:
                    return (Begin(stmts, e_exp), e_temp)
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
                (e, e_temp) = self.rco_exp(exp, False)
                stmts = [Assign([name], value) for name, value in e_temp]
                stmts.append(Assign([Name(var)], e))

                return stmts
            case If(exp, s1, s2):
                (e, e_temp) = self.rco_exp(exp, False)
                stmts = [Assign([name], value) for name, value in e_temp]

                s1_stmts = []
                for s in s1:
                    s1_stmts.extend(self.rco_stmt(s))

                s2_stmts = []
                for s in s2:
                    s2_stmts.extend(self.rco_stmt(s))

                stmts.append(If(e, s1_stmts, s2_stmts))

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
            case Assign([Name(var)], BinOp(atm_a, op, atm_b)):
                if str(op) == "+":
                    op_instr = "addq"
                elif str(op) == "-":
                    op_instr = "subq"
                else:
                    raise Exception("Unsupported binary op in assign: ", s)

                a_arg, b_arg = self.select_arg(atm_a), self.select_arg(atm_b)
                if str(a_arg) == var:
                    return [Instr(op_instr, [b_arg, Variable(var)])]
                elif str(b_arg) == var:
                    return [Instr(op_instr, [a_arg, Variable(var)])]
                else:
                    return [
                        Instr("movq", [a_arg, Variable(var)]),
                        Instr(op_instr, [b_arg, Variable(var)]),
                    ]

            case Assign([Name(var)], UnaryOp(USub(), atm)):
                return [
                    Instr("movq", [self.select_arg(atm), Variable(var)]),
                    Instr("negq", [Variable(var)]),
                ]
            case Assign([Name(var)], Call(Name("input_int"), [])):
                return [
                    Callq(label_name("read_int"), 0),
                    Instr("movq", [Reg("rax"), Variable(var)]),
                ]
            case Assign([Name(var)], atm_exp):
                return [Instr("movq", [self.select_arg(atm_exp), Variable(var)])]

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
        match a:
            # The only case we care about
            case Variable(_):
                home_arg = home.get(a)

                if home_arg:
                    return home_arg
                else:
                    arg = Deref("rbp", -8 * (len(home) + 1))
                    home[a] = arg
                    return arg
            case _:
                return a

    def assign_homes_instr(self, i: instr, home: dict[Variable, arg]) -> instr:
        match i:
            case Instr(op, args):
                return Instr(op, [self.assign_homes_arg(arg, home) for arg in args])
            case Callq(_, _) | Jump():
                return i

    def assign_homes_instrs(
        self, ss: list[instr], home: dict[Variable, arg]
    ) -> list[instr]:
        return [self.assign_homes_instr(instr, home) for instr in ss]

    def assign_homes(self, p: X86Program) -> X86Program:
        home = {}
        assigned = self.assign_homes_instrs(p.body, home)
        num_vars = len(home)
        frame_size = (num_vars + 1) * 8 if num_vars % 2 != 0 else num_vars * 8

        return X86Program(assigned, frame_size)

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        match i:
            case Instr(op, [arg1, arg2]):
                need_patch = False
                match (arg1, arg2):
                    case (Deref(_, _), Deref(_, _)):
                        need_patch = True
                    case (Immediate(v), Deref(_, _)) if v > 2**16:
                        need_patch = True

                return (
                    [Instr("movq", [arg1, Reg("rax")]), Instr(op, [Reg("rax"), arg2])]
                    if need_patch
                    else [i]
                )
            case _:
                return [i]

    def patch_instrs(self, ss: list[instr]) -> list[instr]:
        return [i for instr in ss for i in self.patch_instr(instr)]

    def patch_instructions(self, p: X86Program) -> X86Program:
        return X86Program(self.patch_instrs(p.body))

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        return X86Program(
            [
                Instr("pushq", [Reg("rbp")]),
                Instr("movq", [Reg("rsp"), Reg("rbp")]),
                Instr("subq", [Immediate(p.frame_size), Reg("rsp")]),
                *p.body,
                Instr("addq", [Immediate(p.frame_size), Reg("rsp")]),
                Instr("popq", [Reg("rbp")]),
                Instr("retq", []),
            ]
        )
