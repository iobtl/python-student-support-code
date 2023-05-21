import compiler
from graph import UndirectedAdjList
from ast import *
from x86_ast import *
from typing import Set

# Skeleton code for the chapter on Register Allocation
#
CALLER_SAVED_REG = [
    Reg("rax"),
    Reg("rcx"),
    Reg("rdx"),
    Reg("rsi"),
    Reg("rdi"),
    Reg("r8"),
    Reg("r9"),
    Reg("r10"),
    Reg("r11"),
]

CALLEE_SAVED_REG = [
    Reg("rsp"),
    Reg("rbp"),
    Reg("rbx"),
    Reg("r12"),
    Reg("r13"),
    Reg("r14"),
    Reg("r15"),
]

FUNCTION_REG = [
    Reg("rdi"),
    Reg("rsi"),
    Reg("rdx"),
    Reg("rcx"),
    Reg("r8"),
    Reg("r9"),
]


class Compiler(compiler.Compiler):
    ###########################################################################
    # Uncover Live
    ###########################################################################

    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr("movq", [arg, _]) | Instr(
                "negq" | "pushq", [arg]
            ) if not isinstance(arg, Immediate):
                return set((arg,))
            case Instr("addq" | "subq", args):
                return set([arg for arg in args if not isinstance(arg, Immediate)])
            case Callq(_, num_args):
                # TODO: handle spills
                return set(FUNCTION_REG[0:num_args])
            case _:
                return set()

    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr(_, [_, arg]) | Instr("popq", [arg]):
                return set((arg,))
            case Callq(_, _):
                # All caller-saved registers may be written to
                return set(CALLER_SAVED_REG)
            case _:
                return set()

    def uncover_live(self, p: X86Program) -> dict[instr, Set[location]]:
        """Returns mapping for each instruction to its live-after set."""
        mapping = {}
        num_instr = len(p.body)
        # L_before of (k+1)-th instruction is L_after of k-th instruction
        # Live-after set for last instruction is empty
        l_before = self.read_vars(p.body[num_instr - 1])
        l_after = set()
        mapping[num_instr] = l_after

        for i in range(num_instr - 2, -1, -1):
            instr = p.body[i]
            l_after = l_before
            l_before = l_after.difference(self.write_vars(instr)).union(
                self.read_vars(instr)
            )
            mapping[i + 1] = l_after

        return mapping

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(
        self, p: X86Program, live_after: dict[instr, Set[location]]
    ) -> UndirectedAdjList:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Allocate Registers
    ############################################################################

    # Returns the coloring and the set of spilled variables.
    def color_graph(
        self, graph: UndirectedAdjList, variables: Set[location]
    ) -> tuple[dict[location, int], Set[location]]:
        # YOUR CODE HERE
        pass

    def allocate_registers(self, p: X86Program, graph: UndirectedAdjList) -> X86Program:
        # YOUR CODE HERE
        pass

    ############################################################################
    # assign Homes
    ############################################################################

    def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass

    ###########################################################################
    # Patch Instructions
    ###########################################################################

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass

    ###########################################################################
    # Prelude & Conclusion
    ###########################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass


if __name__ == "__main__":
    prog = """
v = 1
w = 42
x = v + 7
y = x
z = x + w
print(z + (-y))
    """
    import pprint

    pp = pprint.PrettyPrinter(indent=2)

    print("=====AST=====")
    pp.pprint(dump(parse(prog)))

    p = parse(prog)
    c = Compiler()
    p = c.remove_complex_operands(p)
    print("=====RCO=====")
    pp.pprint(p)
    p = c.select_instructions(p)

    a = c.uncover_live(p)

    print("=====Instruction Selection=====")
    pp.pprint(p)
    print("=====Liveness Analysis=====")
    pp.pprint(a)
