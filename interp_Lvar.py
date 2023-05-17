from ast import *
from utils import input_int
from interp_Lint import InterpLint


class InterpLvar(InterpLint):
    def interp_exp(self, e, env):
        match e:
            case Name(id):
                return env[id]
            case _:
                return super().interp_exp(e, env)

    def interp_stmt(self, s, env, cont):
        match s:
            case Assign([Name(id)], value):
                env[id] = self.interp_exp(value, env)
                return self.interp_stmts(cont, env)
            case _:
                return super().interp_stmt(s, env, cont)

    def interp(self, p):
        match p:
            case Module(body):
                self.interp_stmts(body, {})
            case _:
                raise Exception("interp: unexpected " + repr(p))


if __name__ == "__main__":
    # eight = Constant(8)
    # neg_eight = UnaryOp(USub(), eight)
    # read = Call(Name("input_int"), [])
    # ast1_1 = BinOp(read, Add(), neg_eight)
    # pr = Expr(Call(Name("print"), [ast1_1]))
    # p = Module([pr])
    # interp = InterpLvar()
    # interp.interp_Lvar(p)

    c1 = Constant(42)
    c2 = Constant(10)
    c3 = UnaryOp(USub(), c2)
    c4 = BinOp(c1, Add(), c3)
    x = Assign([Name("x")], c4)
    pr = Expr(Call(Name("print"), [BinOp(Name("x"), Add(), c2)]))
    p = Module([x, pr])
    print(repr(p))

    interp = InterpLvar()
    interp.interp(p)

    from compiler import Compiler

    c = Compiler()
    print(c.remove_complex_operands(p))
