# Convert from the x86 AST classes defined in utils.py into the parse
# tree format used by the interpreter.

from ast import Constant, Name, FunctionDef

from lark import Tree
from utils import GlobalValue, FunRef, label_name
from x86_ast import *


def convert_int(value):
    return Tree("int_a", [value])
    # if value >= 0:
    #     return Tree("int_a", [value])
    # else:
    #     return Tree("neg_a", [Tree("int_a", [-value])])


def convert_arg(arg):
    match arg:
        case Reg(id):
            return Tree("reg_a", [id])
        case Variable(id):
            return Tree("var_a", [id])
        case Immediate(value):
            return convert_int(value)
        case Deref(reg, offset):
            return Tree("mem_a", [convert_int(offset), reg])
        case ByteReg(id):
            return Tree("reg_a", [id])
        case Global(id):
            return Tree("global_val_a", [id, "rip"])
        case FunRef(label, _):
            return Tree("var_a", [label])
        case _:
            raise Exception("convert_arg: unhandled " + repr(arg))


def convert_instr(instr):
    match instr:
        case Instr(instr, args):
            return Tree(instr, [convert_arg(arg) for arg in args])
        case Callq(func, args):
            return Tree("callq", [func])
        case IndirectCallq(func, args):
            # Func is either a Variable location of register
            return Tree("indirect_callq", [convert_arg(func)])
        case Jump(label):
            return Tree("jmp", [label])
        case JumpIf(cc, label):
            return Tree("j" + cc, [label])
        case _:
            raise Exception("error in convert_instr, unhandled " + repr(instr))


def convert_program(p):
    if hasattr(p, "body") and isinstance(p.body, list):
        main_instrs = [convert_instr(instr) for instr in p.body]
        main_block = Tree("block", [label_name("main")] + main_instrs)
        return Tree("prog", [main_block])
    elif hasattr(p, "body") and isinstance(p.body, dict):
        blocks = []
        for l, ss in p.body.items():
            blocks.append(Tree("block", [l] + [convert_instr(instr) for instr in ss]))
        return Tree("prog", blocks)
    elif hasattr(p, "defs") and isinstance(p.defs, list):
        blocks = []
        for _def in p.defs:
            match _def:
                case FunctionDef(_, [], body, [], _):
                    for l, ss in body.items():
                        blocks.append(
                            Tree("block", [l] + [convert_instr(instr) for instr in ss])
                        )
                case _:
                    raise Exception("Can only convert function defs.")

        return Tree("prog", blocks)
