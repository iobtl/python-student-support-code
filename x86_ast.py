from __future__ import annotations

import ast
from dataclasses import dataclass
import functools
from typing import Iterable

from utils import dedent, indent, indent_stmt, label_name


@dataclass
class X86Program:
    body: dict[str, list[instr]] | list[instr]
    frame_size: int = 0
    root_spills: int = 0

    def __str__(self):
        result = ""
        if isinstance(self.body, dict):
            for l, ss in self.body.items():
                if l == label_name("main"):
                    result += "\t.globl " + label_name("main") + "\n"
                result += "\t.align 16\n"
                result += l + ":\n"
                indent()
                result += "".join([str(s) for s in ss]) + "\n"
                dedent()
        else:
            result += (
                "\t.globl " + label_name("main") + "\n" + label_name("main") + ":\n"
            )
            indent()
            result += "".join([str(s) for s in self.body])
            dedent()
        result += "\n"
        return result


@dataclass
class X86ProgramDefs:
    defs: list[ast.FunctionDef]
    frame_size: int = 0
    root_spills: int = 0

    def __str__(self):
        return "\n".join([str(d) for d in self.defs])

    @property
    def blocks(self):
        if not hasattr(self, "_blocks"):
            self._blocks = {
                k: v
                for _def in self.defs
                if type(_def) is ast.FunctionDef
                for k, v in _def.body.items()
            }

        return self._blocks

    @property
    def var_types(self):
        if not hasattr(self.defs[0], "var_types"):
            raise Exception("Type checking not done, var_types not present")

        if not hasattr(self, "_var_types"):
            self._var_types = {
                k: v
                for _def in self.defs
                if type(_def) is ast.FunctionDef
                for k, v in _def.var_types.items()
            }

        return self._var_types


class instr:
    ...


class arg:
    ...


class location(arg):
    ...


@dataclass(frozen=True, eq=False)
class Instr(instr):
    instr: str
    args: tuple[arg, ...]

    def __init__(self, name: str, args: Iterable[arg]):
        # https://docs.python.org/3/library/dataclasses.html#frozen-instances
        object.__setattr__(self, "instr", name)
        object.__setattr__(self, "args", tuple(args))

    def source(self):
        return self.args[0]

    def target(self):
        return self.args[-1]

    def __str__(self):
        return (
            indent_stmt()
            + self.instr
            + " "
            + ", ".join(str(a) for a in self.args)
            + "\n"
        )


@dataclass(frozen=True, eq=False)
class Callq(instr):
    func: str
    num_args: int

    def __str__(self):
        return indent_stmt() + "callq" + " " + self.func + "\n"


@dataclass(frozen=True, eq=False)
class IndirectCallq(instr):
    func: arg
    num_args: int

    def __str__(self):
        return indent_stmt() + "callq" + " *" + str(self.func) + "\n"


@dataclass(frozen=True, eq=False)
class JumpIf(instr):
    cc: str
    label: str

    def __str__(self):
        return indent_stmt() + "j" + self.cc + " " + self.label + "\n"


@dataclass(frozen=True, eq=False)
class Jump(instr):
    label: str

    def __str__(self):
        return indent_stmt() + "jmp " + self.label + "\n"


@dataclass(frozen=True, eq=False)
class IndirectJump(instr):
    target: location

    def __str__(self):
        return indent_stmt() + "jmp *" + str(self.target) + "\n"


@dataclass(frozen=True, eq=False)
class TailJump(instr):
    func: arg
    arity: int

    def __str__(self):
        return indent_stmt() + "tailjmp " + str(self.func) + "\n"


@dataclass(frozen=True)
class Variable(location):
    id: str

    def __str__(self):
        return self.id


@dataclass(frozen=True)
class Immediate(arg):
    value: int

    def __str__(self):
        return "$" + str(self.value)


@dataclass(frozen=True)
class Reg(location):
    id: str

    def __str__(self):
        return "%" + self.id


@dataclass(frozen=True)
class ByteReg(Reg):
    pass


@dataclass(frozen=True)
class Deref(arg):
    reg: str
    offset: int

    def __str__(self):
        return str(self.offset) + "(%" + self.reg + ")"


@dataclass(frozen=True)
class Global(arg):
    name: str

    def __str__(self):
        return self.name + "(%rip)"
