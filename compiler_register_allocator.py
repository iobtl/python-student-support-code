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

ALLOCATION = {
    0: Reg("rcx"),
    1: Reg("rdx"),
    2: Reg("rsi"),
    3: Reg("rdi"),
    4: Reg("r8"),
    5: Reg("r9"),
    6: Reg("r10"),
    7: Reg("rbx"),
    8: Reg("r12"),
    9: Reg("r13"),
    10: Reg("r14"),
}


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
            mapping[instr] = l_after

        return mapping

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(
        self, p: X86Program, live_after: dict[instr, Set[location]]
    ) -> UndirectedAdjList:
        i_graph = UndirectedAdjList()
        for instr in p.body:
            match instr:
                case Instr("movq", [arg1, arg2]):
                    for v in live_after.get(instr, []):
                        if v != arg1 and v != arg2:
                            i_graph.add_edge(arg2, v)
                case _:
                    for d in self.write_vars(instr):
                        for v in live_after.get(instr, []):
                            if d != v:
                                i_graph.add_edge(d, v)

        return i_graph

    ############################################################################
    # Allocate Registers
    ############################################################################

    # Returns the coloring and the set of spilled variables.
    def color_graph(
        self, graph: UndirectedAdjList, variables: Set[location]
    ) -> tuple[dict[location, int], Set[location]]:
        vertices = set(graph.vertices())
        saturations = {i: set() for i in vertices}
        reg_ints = {i for i in range(12)}
        allocations = {}
        spilled = set()

        while len(vertices) > 0:
            highest_saturation = {}
            highest_saturation_vertex = 0
            num_highest_saturations = -1

            for v in vertices:
                v_saturations = saturations[v]
                num_saturations = len(v_saturations)
                if num_saturations > num_highest_saturations:
                    num_highest_saturations = num_saturations
                    highest_saturation = v_saturations
                    highest_saturation_vertex = v

            available_regs = reg_ints.difference(highest_saturation)
            if len(available_regs) == 0:
                spilled.add(highest_saturation_vertex)
            else:
                reg_alloc = min(available_regs)
                allocations[highest_saturation_vertex] = reg_alloc
                # Update saturations of adjacent nodes
                for adj in graph.adjacent(highest_saturation_vertex):
                    saturations[adj].add(reg_alloc)

            vertices.remove(highest_saturation_vertex)

        return (allocations, spilled)

    def allocate_registers(self, p: X86Program, graph: UndirectedAdjList) -> X86Program:
        (colored, spilled) = self.color_graph(graph, set())

        # Map first k colors to the k registers and the remaining to the stack
        variable_reg_alloc = {v: ALLOCATION[i] for v, i in colored.items()}
        new_instrs = self.assign_homes_instrs(p.body, variable_reg_alloc)
        num_vars = len(graph.vertices())
        frame_size = (num_vars + 1) * 8 if num_vars % 2 != 0 else num_vars * 8

        return X86Program(new_instrs, frame_size)

    ############################################################################
    # assign Homes
    ############################################################################

    def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
        live_after = self.uncover_live(pseudo_x86)
        ig = self.build_interference(pseudo_x86, live_after)

        return self.allocate_registers(pseudo_x86, ig)

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
    print("=====Instruction Selection=====")
    pp.pprint(p)

    a = c.uncover_live(p)
    print("=====Liveness Analysis=====")
    pp.pprint(a)

    ig = c.build_interference(p, a)
    print("=====Interference Graph=====")
    # ig.show().render(view=True)

    (colored, _) = c.color_graph(ig, set())
    print("=====Graph Coloring=====")
    pp.pprint(colored)

    alloc = c.allocate_registers(p, ig)
    print("=====Register Allocation=====")
    pp.pprint(alloc)
