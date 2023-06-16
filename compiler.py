import ast
import itertools
import os

from ast import *
from type_check_Lfun import TypeCheckLfun
from type_check_Ctup import TypeCheckCtup
from typing import NamedTuple
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
        """Minor modifications to aid later passes.

        Currently does two things:
        1. Converts all `and` and `or` expressions to `IfExp` expressions
        2. Introduces explicit `main` function that wraps all top-level statements
           in the interpreted module.
        """

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
                    return IfExp(_shrink_exp(e), _shrink_exp(s1), _shrink_exp(s2))
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
                case Expr(Call(Name("print"), [e])):
                    return Expr(Call(Name("print"), [_shrink_exp(e)]))
                case Expr(e):
                    return Expr(_shrink_exp(e))
                case While(e, stmts, []):
                    return While(_shrink_exp(e), [_shrink_stmt(s) for s in stmts], [])
                case _:
                    return s

        function_defs = []
        top_level_stmts = []
        for s in p.body:
            if type(s) == FunctionDef:
                function_defs.append(s)
            else:
                top_level_stmts.append(s)

        return Module(
            [
                *function_defs,
                FunctionDef("main", [], top_level_stmts, [], VoidType()),
            ]
        )

    ############################################################################
    # Reveal Functions
    ############################################################################

    def reveal_functions(self, p: Module) -> Module:
        """Converts Name(f) to FunRef(f, n) for function names."""

        def _reveal_exp(e: expr) -> expr:
            match e:
                case Name(v):
                    arity = function_names.get(v)
                    if arity:
                        return FunRef(v, arity)
                    else:
                        return e
                case Call(n, args):
                    return Call(_reveal_exp(n), [_reveal_exp(arg) for arg in args])
                case UnaryOp(op, exp):
                    return UnaryOp(op, _reveal_exp(exp))
                case BinOp(a, op, b):
                    return BinOp(_reveal_exp(a), op, _reveal_exp(b))
                case Compare(a, op, [b]):
                    return Compare(_reveal_exp(a), op, _reveal_exp(b))
                case IfExp(cond, a, b):
                    return IfExp(_reveal_exp(cond), _reveal_exp(a), _reveal_exp(b))
                case Tuple(exprs, Load()):
                    return Tuple([_reveal_exp(expr) for expr in exprs], Load())
                case Subscript(exp, const, Load()):
                    return Subscript(_reveal_exp(exp), const, Load())
                case _:
                    return e

        def _reveal_stmt(s: stmt) -> stmt:
            match s:
                case FunctionDef("main", _, stmts, _, ret):
                    return FunctionDef(
                        "main", [], [_reveal_stmt(stmt) for stmt in stmts], [], ret
                    )
                case Expr(e):
                    return Expr(_reveal_exp(e))
                case Assign(lhs, e):
                    return Assign(lhs, _reveal_exp(e))
                case If(cond, body, orelse):
                    return If(
                        _reveal_exp(cond),
                        [_reveal_stmt(a) for a in body],
                        [_reveal_stmt(b) for b in orelse],
                    )
                case While(cond, body, []):
                    return While(_reveal_exp(cond), [_reveal_stmt(a) for a in body], [])
                case Return(e):
                    if e:
                        return Return(_reveal_exp(e))
                    else:
                        return s
                case _:
                    return s

        function_names = {}
        match p:
            case Module(body):
                # Identify functions
                for s in body:
                    match s:
                        case FunctionDef(name, args, _, _, _):
                            function_names[name] = len(args)
                        case _:
                            pass

                return Module([_reveal_stmt(s) for s in body])
            case _:
                pass

    ############################################################################
    # Limit Functions
    ############################################################################

    def limit_functions(self, p: Module) -> Module:
        """Packs excess parameters (6th onwards) into a tuple."""

        def _replace_names_expr(e: expr, replacement: dict[str, expr]) -> expr:
            match e:
                case Name(n):
                    return replacement.get(n, e)
                case Call(n, args):
                    return Call(
                        _replace_names_expr(n, replacement),
                        [_replace_names_expr(a, replacement) for a in args],
                    )
                case UnaryOp(op, exp):
                    return UnaryOp(op, _replace_names_expr(exp, replacement))
                case BinOp(a, op, b):
                    return BinOp(
                        _replace_names_expr(a, replacement),
                        op,
                        _replace_names_expr(b, replacement),
                    )
                case BoolOp(op, [a, b]):
                    return BoolOp(
                        op,
                        [
                            _replace_names_expr(a, replacement),
                            _replace_names_expr(b, replacement),
                        ],
                    )
                case Compare(a, op, [b]):
                    return Compare(
                        _replace_names_expr(a, replacement),
                        op,
                        [_replace_names_expr(b, replacement)],
                    )
                case IfExp(cond, a, b):
                    return IfExp(
                        _replace_names_expr(cond, replacement),
                        _replace_names_expr(a, replacement),
                        _replace_names_expr(b, replacement),
                    )
                case Tuple(exprs, Load()):
                    return Tuple(
                        [_replace_names_expr(exp, replacement) for exp in exprs], Load()
                    )
                case Subscript(e, const, Load()):
                    return Subscript(_replace_names_expr(e, replacement), const, Load())
                case _:
                    return e

        def _replace_names_stmt(s: stmt, replacement: dict[str, expr]) -> stmt:
            match s:
                case Expr(e):
                    return Expr(_replace_names_expr(e, replacement))
                case Assign(lhs, e):
                    return Assign(lhs, _replace_names_expr(e, replacement))
                case If(cond, body, orelse):
                    return If(
                        _replace_names_expr(cond, replacement),
                        [_replace_names_stmt(a, replacement) for a in body],
                        [_replace_names_stmt(b, replacement) for b in orelse],
                    )
                case While(cond, body, []):
                    return While(
                        _replace_names_expr(cond, replacement),
                        [_replace_names_stmt(a, replacement) for a in body],
                        [],
                    )
                case Return(e):
                    if e:
                        return Return(_replace_names_expr(e, replacement))
                    else:
                        return s
                case _:
                    return s

        new_p = []
        for s in p.body:
            match s:
                case FunctionDef(name, args, body, dec, ret):
                    if len(args) < 6:
                        new_p.append(s)
                        continue

                    packed_args = Tuple(args[5:], Load())
                    replacement: dict[str, expr] = {
                        n.arg: Subscript(packed_args, Constant(i), Load())
                        for i, n in enumerate(args[5:])
                    }
                    new_body = [_replace_names_stmt(b, replacement) for b in body]

                    new_p.append(
                        FunctionDef(name, [*args[:5], packed_args], new_body, dec, ret)
                    )
                case Call(n, args):
                    new_p.append(
                        Call(
                            n,
                            [
                                *args[:5],
                                Tuple(args[5:], Load()),
                            ],
                        )
                    )
                case _:
                    new_p.append(s)

        return Module(new_p)

    ############################################################################
    # Expose Allocation
    ############################################################################
    def expose_exp(self, e: expr) -> expr:
        def _match_expr_ty(e: expr) -> Type:
            match e:
                case Constant(v) if isinstance(v, bool):
                    return BoolType()
                case Constant(v) if isinstance(v, int):
                    return IntType()
                case Name(v):
                    return getattr(v, "has_type", AnyType())
                case Call(Name("input_int"), _):
                    # TODO: function type?
                    return IntType()
                case UnaryOp(USub(), _) | BinOp(_, Add() | Sub(), _):
                    return IntType()
                case BoolOp(_, [_, _]) | UnaryOp(Not(), _) | Compare(_, [_], _):
                    return BoolType()
                case IfExp(_, body, _):
                    # Both branches should return same type
                    return _match_expr_ty(body)
                case Begin(_, ret):
                    return _match_expr_ty(ret)
                case Allocate(_, ty):
                    return ty
                case Tuple(elts, _):
                    return TupleType([_match_expr_ty(e) for e in elts])
                case _:
                    # TODO:
                    return VoidType()

        match e:
            case Tuple(elts, Load()):
                n_elts = len(elts)
                bytes_required = 8 + n_elts * 8
                tmp_names = [generate_name("tuple_tmp") for _ in elts]
                inits = [
                    Assign([Name(n)], self.expose_exp(e))
                    for n, e in zip(tmp_names, elts)
                ]

                free_ptr_after_alloc = BinOp(
                    GlobalValue("free_ptr"), Add(), Constant(bytes_required)
                )
                gc_check = Compare(
                    free_ptr_after_alloc, [GtE()], [GlobalValue("fromspace_end")]
                )
                gc_if = If(gc_check, [Collect(bytes_required)], [])

                alloc = Allocate(
                    n_elts,
                    getattr(
                        e, "has_type", TupleType([_match_expr_ty(e) for e in elts])
                    ),
                )
                tup = generate_name("tuple")
                tup_assign = Assign([Name(tup)], alloc)

                tup_inits = [
                    Assign([Subscript(Name(tup), Constant(i), Store())], Name(tmp_name))
                    for i, tmp_name in enumerate(tmp_names)
                ]
                return Begin(
                    [
                        *inits,
                        gc_if,
                        tup_assign,
                        *tup_inits,
                    ],
                    Name(tup),
                )
            case _:
                return e

    def expose_stmt(self, s: stmt) -> stmt:
        match s:
            case Expr(Call(Name("print"), [e])):
                return Expr(Call(Name("print"), [self.expose_exp(e)]))
            case Expr(e):
                return Expr(self.expose_exp(e))
            case Assign([Name(n)], e):
                return Assign([Name(n)], self.expose_exp(e))
            case If(e, body, orelse):
                return If(
                    self.expose_exp(e),
                    [self.expose_stmt(stmt) for stmt in body],
                    [self.expose_stmt(stmt) for stmt in orelse],
                )
            case While(e, stmts, []):
                return While(
                    self.expose_exp(e), [self.expose_stmt(stmt) for stmt in stmts], []
                )
            case _:
                return s

    def expose_allocation(self, p: Module) -> Module:
        """Converts tuple creation into making conditional call to GC.

        Possibly triggers garbage collection on top of the required allocation.
        """
        # HACK: running typechecker to populate has_type field of Tuple AST nodes...
        TypeCheckLfun().type_check(p)

        match p:
            case Module(body):
                return Module([self.expose_stmt(s) for s in body])
            case _:
                pass

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr, Temporaries]:
        match e:
            case Constant(_) | Name(_) | GlobalValue(_):
                return (e, [])
            case Call(Name("input_int"), []):
                ret = e
                if need_atomic:
                    i = Name(generate_name("input"))
                    return (i, [(i, ret)])
                else:
                    return (ret, [])
            case Call(Name("len"), [e]):
                (e_exp, e_temp) = self.rco_exp(e, True)
                ret = Call(Name("len"), [e_exp])
                if need_atomic:
                    i = Name(generate_name("len"))
                    return (i, [(i, ret)])
                else:
                    return (ret, e_temp)
            case Compare(a, [cmp], [b]):
                (a_exp, a_temp) = self.rco_exp(a, True)
                (b_exp, b_temp) = self.rco_exp(b, True)

                ret = Compare(a_exp, [cmp], [b_exp])
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (
                        tmp,
                        [*a_temp, *b_temp, (tmp, ret)],
                    )
                else:
                    return (ret, [*a_temp, *b_temp])
            case UnaryOp(USub(), v):
                (v_exp, v_temp) = self.rco_exp(v, True)

                ret = UnaryOp(USub(), v_exp)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*v_temp, (tmp, ret)])
                else:
                    return (ret, v_temp)
            case UnaryOp(Not(), v):
                (v_exp, v_temp) = self.rco_exp(v, False)

                ret = UnaryOp(Not(), v_exp)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*v_temp, (tmp, ret)])
                else:
                    return (ret, v_temp)
            case BinOp(a, Add(), b):
                (a_exp, a_temp) = self.rco_exp(a, True)
                (b_exp, b_temp) = self.rco_exp(b, True)

                ret = BinOp(a_exp, Add(), b_exp)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*a_temp, *b_temp, (tmp, ret)])
                else:
                    return (ret, [*a_temp, *b_temp])
            case BinOp(a, Sub(), b):
                (a_exp, a_temp) = self.rco_exp(a, True)
                (b_exp, b_temp) = self.rco_exp(b, True)

                ret = BinOp(a_exp, Sub(), b_exp)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*a_temp, *b_temp, (tmp, ret)])
                else:
                    return (ret, [*a_temp, *b_temp])
            case IfExp(cond, e1, e2):
                (cond_exp, cond_temp) = self.rco_exp(cond, False)
                (e1_exp, e1_temp) = self.rco_exp(e1, False)
                (e2_exp, e2_temp) = self.rco_exp(e2, False)

                ret = IfExp(cond_exp, e1_exp, e2_exp)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (
                        tmp,
                        [
                            *cond_temp,
                            *e1_temp,
                            *e2_temp,
                            (tmp, ret),
                        ],
                    )
                else:
                    return (
                        ret,
                        [*cond_temp, *e1_temp, *e2_temp],
                    )
            case Subscript(e1, e2, Load()):
                (e1_exp, e1_temp) = self.rco_exp(e1, True)
                (e2_exp, e2_temp) = self.rco_exp(e2, True)

                ret = Subscript(e1_exp, e2_exp, Load())
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (
                        tmp,
                        [*e1_temp, *e2_temp, (tmp, ret)],
                    )
                else:
                    return (ret, [*e1_temp, *e2_temp])
            case Allocate(_, _):
                if need_atomic:
                    alloc = Name(generate_name("alloc"))
                    return (alloc, [(alloc, e)])
                else:
                    return (e, [])
            case Begin(stmts, e):
                (e_exp, e_temp) = self.rco_exp(e, False)
                ret = Begin(
                    [s for body_stmt in stmts for s in self.rco_stmt(body_stmt)], e_exp
                )
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    return (tmp, [*e_temp, (tmp, ret)])
                else:
                    # TODO:
                    return (ret, e_temp)
            case _:
                raise Exception("Unsupported expression: ", e)

    def rco_stmt(self, s: stmt) -> list[stmt]:
        match s:
            case Expr(Call(Name("print"), [exp])):
                (e, e_temp) = self.rco_exp(exp, True)
                stmts: list[stmt] = [Assign([name], value) for name, value in e_temp]
                stmts.append(Expr(Call(Name("print"), [e])))

                return stmts
            case Expr(exp):
                (e, e_temp) = self.rco_exp(exp, False)
                stmts: list[stmt] = [Assign([name], value) for name, value in e_temp]
                stmts.append(Expr(e))

                return stmts
            case Assign([Name(var)], exp):
                (e, e_temp) = self.rco_exp(exp, False)
                stmts: list[stmt] = [Assign([name], value) for name, value in e_temp]
                stmts.append(Assign([Name(var)], e))

                return stmts
            case Assign([Subscript(value, idx, Store())], exp):
                (e, e_temp) = self.rco_exp(exp, True)
                (i, i_temp) = self.rco_exp(idx, True)
                (v, v_temp) = self.rco_exp(value, True)

                stmts: list[stmt] = [
                    Assign([name], value)
                    for name, value in itertools.chain(e_temp, i_temp, v_temp)
                ]
                stmts.append(Assign([Subscript(v, i, Store())], e))

                return stmts
            case If(exp, s1, s2):
                (e, e_temp) = self.rco_exp(exp, False)
                stmts: list[stmt] = [Assign([name], value) for name, value in e_temp]

                s1_stmts: list[stmt] = []
                for s in s1:
                    s1_stmts.extend(self.rco_stmt(s))

                s2_stmts: list[stmt] = []
                for s in s2:
                    s2_stmts.extend(self.rco_stmt(s))

                stmts.append(If(e, s1_stmts, s2_stmts))

                return stmts
            case While(exp, body, []):
                (e, e_temp) = self.rco_exp(exp, False)
                stmts: list[stmt] = [Assign([name], value) for name, value in e_temp]

                body_rco: list[stmt] = []
                for body_stmt in body:
                    body_rco.extend(self.rco_stmt(body_stmt))

                stmts.append(While(e, body_rco, []))

                return stmts
            case Collect(_):
                return [s]
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
            case Begin(body, result):
                pred = [Assign([lhs], result)] + cont.copy()
                for i in range(len(body) - 1, -1, -1):
                    pred = self.explicate_stmt(body[i], pred, basic_blocks)

                return pred
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
                return self.explicate_pred(v, els_goto, thn_goto, basic_blocks)
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
            case Begin(body, result):
                pred = []
                for i in range(len(body) - 1, -1, -1):
                    pred = self.explicate_stmt(body[i], pred, basic_blocks)

                return [
                    *pred,
                    If(Compare(result, [Eq()], [Constant(False)]), els_goto, thn_goto),
                ]
            case Subscript(a, b, Load()):
                cond_tmp = Name(generate_name("if_tmp"))
                return [Assign([cond_tmp], cond)] + self.explicate_pred(
                    cond_tmp, thn_goto, els_goto, basic_blocks
                )
            case _:
                return [
                    If(Compare(cond, [Eq()], [Constant(False)]), els_goto, thn_goto)
                ]

    def explicate_stmt(
        self, s: stmt, cont: list[stmt], basic_blocks: dict[Label, list[stmt]]
    ) -> list[stmt]:
        """Generates code for statements."""
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case (
                Expr(Call(Name("print"), [_]))
                | Expr(Call(Name("len"), [_]))
                | Expr(Allocate(_, _))
            ):
                # TODO: verify
                return [s, *cont]
            case Expr(v):
                return self.explicate_effect(v, cont, basic_blocks)
            case If(cond, thn, els):
                cont_block = self.create_block(cont, basic_blocks)

                thn_pred = cont_block.copy()
                for i in range(len(thn) - 1, -1, -1):
                    thn_pred = self.explicate_stmt(thn[i], thn_pred, basic_blocks)

                els_pred = cont_block.copy()
                for i in range(len(els) - 1, -1, -1):
                    els_pred = self.explicate_stmt(els[i], els_pred, basic_blocks)

                return self.explicate_pred(cond, thn_pred, els_pred, basic_blocks)
            case While(cond, body, []):
                # Assembly: cmp, j{cc} (to after body), {body}, jmp (to cmp)
                cont_block = self.create_block(cont, basic_blocks)
                loop_block_label = label_name(generate_name("block"))
                body_pred = [Goto(loop_block_label)]
                for i in range(len(body) - 1, -1, -1):
                    body_pred = self.explicate_stmt(body[i], body_pred, basic_blocks)
                body_block = self.create_block(body_pred, basic_blocks)

                if_pred = self.explicate_pred(
                    cond, body_block, cont_block, basic_blocks
                )
                basic_blocks[loop_block_label] = if_pred

                return [Goto(loop_block_label)]
            case Assign([Subscript(_, _, Store())], _) | Collect(_) | Expr():
                return [s, *cont]

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
            case GlobalValue(v):
                return Global(v)
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
                    case Eq() | Is():
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
                    # NOTE: order of comparison is swapped!
                    # a > b -> cmpq a, b; sets g if b > a, e if b == a, l if b < a
                    # This is wrong! So need to swap the both.
                    # AT&T convention sets cmpq a, b based on result of b - a
                    Instr("cmpq", [self.select_arg(b), self.select_arg(a)]),
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
                    case Eq() | Is():
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
            case Assign([Name(var)], Subscript(a, b, Load())):
                match b:
                    case Constant(v):
                        offset = v
                    case _:
                        raise Exception("Subscript index must be a constant: ", s)

                return [
                    Instr("movq", [self.select_arg(a), Reg("r11")]),
                    Instr("movq", [Deref("r11", 8 * (offset + 1)), Variable(var)]),
                ]
            case Assign([Name(var)], Allocate(n, TupleType(tys))):
                # Tag bits info:
                # 0 (1): 1 If tuple has been copied to ToSpace. 0 means entire tag is a forwarding pointer
                # 1-6 (6): Length of tuple
                # 7-56 (50): Pointer mask for elements in the tuple. Note that number of elements limited to 50,
                #            so we only need 50 bits.
                return [
                    Instr("movq", [Global("free_ptr"), Reg("r11")]),
                    Instr(
                        "addq",
                        [Immediate(8 * (n + 1)), Global("free_ptr")],
                    ),
                    # TODO: better bit manipulation?
                    Instr(
                        "movq",
                        [
                            Immediate(
                                (
                                    int(
                                        "1" * n
                                        if any(
                                            isinstance(ty, TupleType | ListType)
                                            for ty in tys
                                        )
                                        else "0" * n
                                    )
                                    << 7
                                )
                                | (n << 1)
                                | 1
                            ),
                            Deref("r11", 0),
                        ],
                    ),
                    Instr("movq", [Reg("r11"), Variable(var)]),
                ]
            case Assign([Name(var)], Call(Name("len"), [Name(v)])):
                return [
                    Instr("movq", [Variable(v), Reg("r11")]),
                    # Length represented in bits 1-6
                    Instr("movq", [Deref("r11", 0), Variable(var)]),
                    Instr("sarq", [Immediate(1), Variable(var)]),
                    Instr("andq", [Immediate(0x2F), Variable(var)]),
                ]
            case Assign([Name(var)], atm_exp):
                return [Instr("movq", [self.select_arg(atm_exp), Variable(var)])]
            case Assign([Subscript(a, b, Store())], v):
                match b:
                    case Constant(n):
                        offset = n
                    case _:
                        raise Exception("Subscript index must be a constant: ", s)

                return [
                    Instr("movq", [self.select_arg(a), Reg("r11")]),
                    Instr("movq", [self.select_arg(v), Deref("r11", 8 * (offset + 1))]),
                ]
            case Collect(n_bytes):
                return [
                    Instr("movq", [Reg("r15"), Reg("rdi")]),
                    Instr("movq", [Immediate(n_bytes), Reg("rsi")]),
                    Callq("collect", 2),
                ]
            case _:
                raise Exception("Unrecognized statement: ", s)

    def select_instructions(self, p: CProgram) -> X86Program:
        tc_ctup = TypeCheckCtup()
        tc_ctup.type_check(p)
        var_types = p.var_types
        p = X86Program(
            {
                label: [instr for stmt in stmts for instr in self.select_stmt(stmt)]
                for label, stmts in p.body.items()
            },
        )
        p.var_types = var_types

        return p

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
