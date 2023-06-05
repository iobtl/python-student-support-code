import ast
import os

from ast import *
from typing import NamedTuple, Set
from graph import DirectedAdjList

from utils import *
from x86_ast import *

Binding = tuple[Name, expr]
Temporaries = list[Binding]
Label = str
Block = list[stmt]


class Compiler:
    ############################################################################
    # Utils
    ############################################################################
    @staticmethod
    def build_cfg(p: X86Program) -> DirectedAdjList:
        cfg = DirectedAdjList()
        for label, block in p.body.items():
            cfg.add_vertex(label)

            for instr in block:
                match instr:
                    # TODO: add conclusion
                    case Jump(l) | JumpIf(_, l) if l != "_conclusion":
                        cfg.add_edge(label, l)

        return cfg

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
                if need_atomic:
                    i = Name(generate_name("input"))
                    return (i, [(i, Call(Name("input_int"), []))])
                else:
                    return (Call(Name("input_int"), []), [])
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
                (e1_exp, e1_temp) = self.rco_exp(e1, False)
                (e2_exp, e2_temp) = self.rco_exp(e2, False)

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
            case While(exp, body, []):
                (e, e_temp) = self.rco_exp(exp, False)
                stmts = [Assign([name], value) for name, value in e_temp]

                body_rco = []
                for stmt in body:
                    body_rco.extend(self.rco_stmt(stmt))

                stmts.append(While(e, body_rco, []))

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
    # Explicate Control
    ############################################################################

    def create_block(
        self, stmts: list[stmt], basic_blocks: dict[Label, list[stmt]]
    ) -> list[Goto]:
        """De-lineates a basic block."""
        match stmts:
            case [Goto(_)]:
                return stmts
            case _:
                label = label_name(generate_name("block"))
                basic_blocks[label] = stmts
                return [Goto(label)]

    def explicate_effect(
        self, e: expr, cont: list[stmt], basic_blocks: dict[Label, list[stmt]]
    ) -> list[stmt]:
        """Generates code for expressions as statements, ignoring the result."""
        match e:
            case IfExp(cond, thn, els):
                thn_e = self.explicate_effect(thn, cont, basic_blocks)
                els_e = self.explicate_effect(els, cont, basic_blocks)
                return self.explicate_pred(cond, thn_e, els_e, basic_blocks)
            case Call(Name("input_int"), _):
                return [Expr(e), *cont]
            case Begin(body, _):
                # TODO: verify
                return body
            case _:
                # Discard result
                return cont

    def explicate_assign(
        self,
        rhs: expr,
        lhs: expr,
        cont: list[stmt],
        basic_blocks: dict[Label, list[stmt]],
    ) -> list[stmt]:
        """Generates code for expressions on the RHS of an assignment."""
        match rhs:
            case IfExp(cond, thn, els):
                cont_block = self.create_block(cont, basic_blocks)
                # If condition passes, assigns result of thn to lhs
                thn_case = self.explicate_assign(thn, lhs, cont_block, basic_blocks)
                # Else, assigns result of els to lhs
                els_case = self.explicate_assign(els, lhs, cont_block, basic_blocks)

                return self.explicate_pred(cond, thn_case, els_case, basic_blocks)
            case Begin(_, _):
                pass
            case _:
                return [Assign([lhs], rhs)] + cont

    def explicate_pred(
        self,
        cond: expr,
        thn: list[stmt],
        els: list[stmt],
        basic_blocks: dict[Label, list[stmt]],
    ) -> list[stmt]:
        """Generates code for an if expression or statement by analyzing the condition expression."""
        thn_goto = self.create_block(thn, basic_blocks)
        els_goto = self.create_block(els, basic_blocks)

        match cond:
            case Compare(_, [_], [_]):
                return [If(cond, thn_goto, els_goto)]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case UnaryOp(Not(), v):
                return [If(Compare(v, [Eq()], [Constant(False)]), thn_goto, els_goto)]
            case IfExp(cond_e, body, orelse):
                # Example: y + 2 if (x == 0 if x < 1 else x == 2) else y + 10
                # Transformed:
                # if x < 1:
                #   if x == 0:
                #       return y + 2
                #   else:
                #       return y + 10
                # else:
                #   if x == 2:
                #       return y + 2
                #   else:
                #       return y + 10
                return self.explicate_pred(
                    cond_e,
                    self.explicate_pred(body, thn_goto, els_goto, basic_blocks),
                    self.explicate_pred(orelse, thn_goto, els_goto, basic_blocks),
                    basic_blocks,
                )
            case Begin(_, _):
                pass
            case _:
                return [
                    If(Compare(cond, [Eq()], [Constant(False)]), els_goto, thn_goto)
                ]

    def explicate_stmt(
        self, s: stmt, cont: list[stmt], basic_blocks: dict[Label, list[stmt]]
    ):
        """Generates code for statements."""
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(Call(Name("print"), [_])):
                # TODO: verify
                return [s, *cont]
            case Expr(v):
                return self.explicate_effect(v, cont, basic_blocks)
            case If(cond, thn, els):
                cont_block = self.create_block(cont, basic_blocks)
                thn_pred = [
                    stmt
                    for thn_stmt in thn
                    for stmt in self.explicate_stmt(thn_stmt, cont_block, basic_blocks)
                ]
                els_pred = [
                    stmt
                    for els_stmt in els
                    for stmt in self.explicate_stmt(els_stmt, cont_block, basic_blocks)
                ]
                return self.explicate_pred(cond, thn_pred, els_pred, basic_blocks)

    def explicate_control(self, p: Module) -> CProgram:
        match p:
            case Module(body):
                new_body = [Return(Constant(0))]
                basic_blocks = {}
                # Process from back to front so that result of each processed stmt
                # is stored in basic_blocks to be used as the *compiled* continuation parameter
                # for the previous statement
                for i in range(len(body) - 1, -1, -1):
                    new_body = self.explicate_stmt(body[i], new_body, basic_blocks)
                basic_blocks[label_name("start")] = new_body

                return CProgram(basic_blocks)

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        match e:
            case Constant(c):
                if isinstance(c, bool):
                    return Immediate(1 if c else 0)
                elif isinstance(c, int):
                    return Immediate(c)
                else:
                    raise Exception("Unsupported constant: ", e)
            case Name(n):
                return Variable(n)
            case _:
                raise Exception("Unsupported atomic expression: ", e)

    def select_stmt(self, s: stmt) -> list[instr]:
        match s:
            case Return(e):
                if e:
                    return [
                        Instr("movq", [self.select_arg(e), Reg("rax")]),
                        Jump(label_name("conclusion")),
                    ]
                else:
                    return [Jump(label_name("conclusion"))]
            case Goto(l):
                return [Jump(l)]
            case If(Compare(a, [cmp], [b]), [Goto(thn)], [Goto(els)]):
                match cmp:
                    case Eq():
                        cmp_op = "e"
                    case Lt():
                        cmp_op = "l"
                    case LtE():
                        cmp_op = "le"
                    case Gt():
                        cmp_op = "g"
                    case GtE():
                        cmp_op = "ge"
                    case _:
                        raise Exception("Unrecognized comparison operator: ", s)

                return [
                    Instr("cmpq", [self.select_arg(a), self.select_arg(b)]),
                    JumpIf(cmp_op, thn),
                    Jump(els),
                ]
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
            case Assign([Name(var)], UnaryOp(Not(), atm)):
                xorq_instr = Instr("xorq", [Immediate(1), Variable(var)])
                if str(atm) == str(var):
                    return [xorq_instr]
                else:
                    return [
                        Instr("movq", [self.select_arg(atm), Variable(var)]),
                        xorq_instr,
                    ]
            case Assign([Name(var)], Compare(a, [cmp], [b])):
                cmp_instr = Instr("cmpq", [self.select_arg(a), self.select_arg(b)])
                mov_instr = Instr("movzbq", [Reg("al"), Variable(var)])

                match cmp:
                    case Eq():
                        cmp_op = "sete"
                    case Lt():
                        cmp_op = "setl"
                    case LtE():
                        cmp_op = "setle"
                    case Gt():
                        cmp_op = "setg"
                    case GtE():
                        cmp_op = "setge"
                    case _:
                        raise Exception("Unrecognized comparison operator: ", s)

                return [cmp_instr, Instr(cmp_op, [Reg("al")]), mov_instr]
            case Assign([Name(var)], Call(Name("input_int"), [])):
                return [
                    Callq(label_name("read_int"), 0),
                    Instr("movq", [Reg("rax"), Variable(var)]),
                ]
            case Assign([Name(var)], atm_exp):
                return [Instr("movq", [self.select_arg(atm_exp), Variable(var)])]
            case _:
                raise Exception("Unrecognized statement: ", s)

    def select_instructions(self, p: CProgram) -> X86Program:
        return X86Program(
            {
                label: [instr for stmt in stmts for instr in self.select_stmt(stmt)]
                for label, stmts in p.body.items()
            }
        )

    ############################################################################
    # Remove Jumps
    ############################################################################

    def remove_jumps(self, p: X86Program) -> X86Program:
        class MergeSet(NamedTuple):
            base: Label
            base_jmp_idx: int
            to_merge: Label

        cfg = Compiler.build_cfg(p)

        in_edges = []
        merge_into: list[MergeSet] = []
        for label, block in p.body.items():
            for idx, instr in enumerate(block):
                match instr:
                    case Jump(l) if l != label_name("conclusion"):
                        for e in cfg.in_edges(l):
                            in_edges.append(e)
                        if len(in_edges) == 1:
                            merge_into.append(MergeSet(label, idx, l))

            in_edges.clear()

        for m in merge_into:
            # TODO: potentially O(n^2)
            (base, base_jmp_idx, to_merge) = m
            old_base_instrs = p.body[base]
            p.body[base] = (
                old_base_instrs[:base_jmp_idx]
                + p.body[to_merge]
                + old_base_instrs[base_jmp_idx + 1 :]
            )

            del p.body[to_merge]

        return p

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        match i:
            case Instr("cmpq", [c, Immediate(v)]):
                # TODO(verify): correct to just assign to another register like that?
                # Second argument of cmpq cannot be constant

                if str(c) == "%rax":
                    reassign_reg = "rcx"
                else:
                    reassign_reg = "rax"

                return [
                    Instr("movq", [Immediate(v), Reg(reassign_reg)]),
                    Instr("cmpq", [c, Reg(reassign_reg)]),
                ]
            case Instr("movzbq", [a, b]) if isinstance(b, Deref) or isinstance(
                b, Immediate
            ):
                # Second argument of movzbq needs to be a register
                return [
                    Instr("movzbq", [a, Reg("rax")]),
                    Instr("movq", [Reg("rax"), b]),
                ]
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
