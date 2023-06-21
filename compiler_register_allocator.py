import compiler
from compiler import Block, Label
from compiler_utils import *
import copy

from graph import DirectedAdjList, UndirectedAdjList, topological_sort, transpose
from dataflow_analysis import analyze_dataflow
from utils import GlobalValue, TupleType
from ast import *
from x86_ast import *
from typing import Callable, Set

# Skeleton code for the chapter on Register Allocation
#


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
            case Instr("addq" | "subq" | "cmpq" | "movzbq" | "xorq", args):
                return set([arg for arg in args if not isinstance(arg, Immediate)])
            case Callq(_, num_args):
                # TODO: handle spills
                return set(FUNCTION_REG[0:num_args])
            case IndirectCallq(target, num_args) | TailJump(target, num_args):
                # TODO: handle spills
                return set([*FUNCTION_REG[0:num_args], target])
            case _:
                return set()

    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr("addq" | "subq" | "movq" | "xorq" | "movzbq", [_, arg]):
                return set((arg,))
            case Instr(op, [arg]) if op not in ["negq", "pushq"]:
                return set((arg,))
            case Callq(_, _) | IndirectCallq(_, _) | TailJump(_, _):
                # All caller-saved registers may be written to
                return set(CALLER_SAVED_REG)
            case _:
                return set()

    def uncover_live(
        self, p: X86ProgramDefs
    ) -> dict[tuple[Label, instr], Set[location]]:
        """Returns mapping for each instruction to its live-after set."""
        blocks = p.blocks

        def _transfer(label: Label, live_after_block: set) -> set:
            """Transfer function for dataflow analysis.

            Note that live_after is simply khe live_before set for a block which
            this current block jumps to.
            Returns live-before set for the analyzed block.
            Also updates live-before and live-after sets for every instruction.
            """
            block = blocks.get(label, [])
            if len(block) == 0:
                # e.g. conclusion block might not have been created yet
                return set()

            last_instr = block[-1]
            live_before = self.read_vars(block[-1])
            match last_instr:
                case JumpIf(_, _) | Jump(_):
                    live_before = live_before.union(live_after_block)

            live_after = live_after_block.copy()
            mapping[(label, block[-1])] = live_after

            for i in range(len(block) - 2, -1, -1):
                instr = block[i]

                match instr:
                    case JumpIf(_, _) | Jump(_):
                        live_after = live_before.union(live_after_block)
                    case _:
                        live_after = live_before

                live_before = live_after.difference(self.write_vars(instr)).union(
                    self.read_vars(instr)
                )
                mapping[(label, instr)] = live_after

            return live_before

        def _join(x: set, y: set) -> set:
            return x.union(y)

        cfg = compiler.Compiler.build_cfg(p)
        mapping = {}
        analyze_dataflow(transpose(cfg), _transfer, set(), _join)

        return mapping

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(
        self, p: X86ProgramDefs, live_after: dict[tuple[Label, instr], Set[location]]
    ) -> UndirectedAdjList:
        var_types = p.var_types
        i_graph = UndirectedAdjList()

        for label, block in p.blocks.items():
            for instr in block:
                match instr:
                    case Instr("movq" | "movzb", [arg1, arg2]):
                        # TODO: extract register from Deref instructions?
                        # PERF: what if `arg2` is assigned to and never used again?
                        for v in live_after.get((label, instr), []):
                            if (
                                isinstance(v, Variable | Reg)
                                and v != arg1
                                and v != arg2
                            ):
                                i_graph.add_edge(arg2, v)

                        continue
                    case Callq(func, _):
                        if func == "collect":
                            # Check for call-live tuple variables
                            for v in live_after.get((label, instr), []):
                                match v:
                                    case Variable(n) if type(var_types[n]) is TupleType:
                                        for reg in CALLEE_SAVED_REG:
                                            i_graph.add_edge(v, reg)
                                    case _:
                                        pass
                    case _:
                        pass

                for d in self.write_vars(instr):
                    for v in live_after.get((label, instr), []):
                        if isinstance(v, Variable | Reg) and d != v:
                            i_graph.add_edge(d, v)

        return i_graph

    ############################################################################
    # Allocate Registers
    ############################################################################

    # Returns the coloring and the set of spilled variables.
    def color_graph(
        self, graph: UndirectedAdjList, variables: Set[location]
    ) -> tuple[dict[location, int], Set[location]]:
        saturations = {}
        vertices = set(i for i in graph.vertices() if type(i) is Variable)

        for v in vertices:
            sats_init: set[int] = set()
            for adj in graph.adjacent(v):
                if type(adj) is Reg and adj.id in REG_NUM_ALLOCATION:
                    sats_init.add(REG_NUM_ALLOCATION[adj.id])

            saturations[v] = sats_init.copy()
            sats_init.clear()

        reg_ints = {i for i in range(len(NUM_REG_ALLOCATION))}
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
                # Update saturations of adjacent nodes if they are variables
                for adj in graph.adjacent(highest_saturation_vertex):
                    if type(adj) is Variable:
                        saturations[adj].add(reg_alloc)

            vertices.remove(highest_saturation_vertex)

        return (allocations, spilled)

    def allocate_registers(
        self, p: X86ProgramDefs, graph: UndirectedAdjList
    ) -> X86ProgramDefs:
        def replace_args(
            mapping: Callable[[arg], location], root_spills: int
        ) -> X86ProgramDefs:
            new_defs = []

            for _def in p.defs:
                match _def:
                    case FunctionDef(var, params, blocks, [], ret):
                        new_instrs = {}
                        for label, block in blocks.items():
                            instrs = []
                            for instr in block:
                                match instr:
                                    case Instr(op, args):
                                        instrs.append(
                                            Instr(
                                                op,
                                                [mapping(a) for a in args],
                                            )
                                        )
                                    case IndirectCallq(func, arity):
                                        instrs.append(
                                            IndirectCallq(mapping(func), arity)
                                        )
                                    case TailJump(func, arity):
                                        instrs.append(TailJump(mapping(func), arity))
                                    case _:
                                        instrs.append(instr)

                            new_instrs[label] = instrs

                        new_def = copy.copy(_def)
                        new_def.body = new_instrs
                        new_defs.append(new_def)

            num_vars = len(graph.vertices())
            frame_size = (num_vars + 1) * 8 if num_vars % 2 != 0 else num_vars * 8

            return X86ProgramDefs(new_defs, frame_size, root_spills)

        if graph.num_vertices() == 0:
            # Only one temporary
            return replace_args(
                lambda a: Reg("rax") if isinstance(a, Variable) else a, 0
            )

        (colored, spilled) = self.color_graph(graph, set())
        root_spills = 0

        # Map first k colors to the k registers and the remaining to the stack
        variable_reg_alloc = {v: NUM_REG_ALLOCATION[i] for v, i in colored.items()}
        # TODO: Spilled vars that don't interfere with each other can be allocated same stack
        # position?
        var_types = p.var_types
        for i, spilled_var in enumerate(spilled):
            match spilled_var:
                case Variable(v) if isinstance(var_types[v], TupleType):
                    variable_reg_alloc[spilled_var] = Deref("r15", -i * 8)
                    root_spills += 1
                case _:
                    variable_reg_alloc[spilled_var] = Deref("rbp", -(i + 1) * 8)

        return replace_args(
            # TODO: verify
            lambda a: variable_reg_alloc.get(a, Reg("rax"))
            if isinstance(a, Variable)
            else a,
            root_spills,
        )

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
        """Ensures at most one argument is memory access and remove trivial moves."""

        def instr_duplicated(i: instr):
            match i:
                case Instr(_, [arg1, arg2]):
                    return arg1 == arg2
                case _:
                    return False

        new_instrs = {
            l: [
                instr
                for instr in self.patch_instrs(block)
                if not instr_duplicated(instr)
            ]
            for l, block in p.body.items()
        }

        return X86Program(new_instrs, p.frame_size, p.root_spills)

    ###########################################################################
    # Prelude & Conclusion
    ###########################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        def align(b: int) -> int:
            if b % 16 == 0:
                return b
            else:
                return b + 8

        used_callee = set()
        spilled_offsets = set()

        # Determine which callee-saved registers were used
        for block in p.body.values():
            for _instr in block:
                match _instr:
                    case Instr(_, args):
                        for arg in args:
                            match arg:
                                case Reg(_):
                                    # r15 is special register for rootstack
                                    if arg in CALLEE_SAVED_REG and arg.id != "r15":
                                        used_callee.add(arg)
                                case Deref("rbp", offset):
                                    spilled_offsets.add(offset)
                                case _:
                                    continue

        num_callee = len(used_callee)
        # Procedure call stack and rootstack separate
        num_spilled = len(spilled_offsets)
        stack_sub = align(8 * num_spilled + 8 * num_callee) - 8 * num_callee

        # Prelude
        main_label = label_name("main")
        main_instrs: list[instr] = [
            Instr("pushq", [Reg("rbp")]),
            Instr("movq", [Reg("rsp"), Reg("rbp")]),
        ]

        new_instrs = {}
        # Save used callee-saved registers
        # NOTE: `pushq` also subtracts from `rsp`
        callee_reg_used = len(used_callee) > 0
        if callee_reg_used:
            for reg in used_callee:
                main_instrs.append(Instr("pushq", [reg]))
            main_instrs.append(Instr("subq", [Immediate(stack_sub), Reg("rsp")]))

        # Initialize rootstack for GC
        main_instrs.extend(
            [
                Instr("movq", [Immediate(65536), Reg("rdi")]),
                Instr("movq", [Immediate(16), Reg("rsi")]),
                Callq("initialize", 2),
                Instr("movq", [Global("rootstack_begin"), Reg("r15")]),
            ]
        )

        for _ in range(p.root_spills):
            main_instrs.extend(
                [
                    # Zero out pointer so GC does not mistake this allocated space
                    # for the tuple-type variable as uninitialized and attempt to collect i
                    Instr("movq", [Immediate(0), Deref("r15", 0)]),
                    # 8 bytes for a pointer to the tuple variable
                    Instr(
                        "addq",
                        [Immediate(8), Reg("r15")],
                    ),
                ]
            )

        # Jump to start
        main_instrs.append(Jump(label_name("start")))
        new_instrs[main_label] = main_instrs

        # Conclusion
        conclusion_label = label_name("conclusion")
        new_instrs[conclusion_label] = [
            Instr("subq", [Immediate(8 * p.root_spills), Reg("r15")])
        ]
        if callee_reg_used:
            new_instrs[conclusion_label].append(
                Instr("addq", [Immediate(stack_sub), Reg("rsp")])
            )
            for reg in used_callee:
                new_instrs[conclusion_label].append(Instr("popq", [reg]))
        new_instrs[conclusion_label].append(Instr("popq", [Reg("rbp")]))
        new_instrs[conclusion_label].append(Instr("retq", []))

        return X86Program(new_instrs | p.body, p.frame_size)


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

    patched = c.patch_instructions(alloc)
    print("=====Patch Instructions=====")
    pp.pprint(patched)

    final = c.prelude_and_conclusion(patched)
    print("=====Prelude and Conclusion=====")
    pp.pprint(final)
