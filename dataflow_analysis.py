from collections import deque
from graph import transpose
from functools import reduce


def analyze_dataflow(G, transfer, bottom, join):
    trans_G = transpose(G)
    # live-before sets of blocks
    mapping = {}
    worklist = deque()
    for v in G.vertices():
        mapping[v] = bottom
        worklist.append(v)

    while worklist:
        node = worklist.pop()
        # Combines live_before of all blocks which the current node jumps to
        # (since this is the transposed CFG)
        input = reduce(join, [mapping[v] for v in trans_G.adjacent(node)], bottom)
        output = transfer(node, input)
        if output != mapping[node]:
            mapping[node] = output
            worklist.extend(G.adjacent(node))

    return mapping
