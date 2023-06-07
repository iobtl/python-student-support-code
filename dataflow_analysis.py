from collections import deque
from graph import transpose
from functools import reduce


def analyze_dataflow(trans_G, transfer, bottom, join):
    G = transpose(trans_G)
    # live-before sets of blocks
    mapping = {}
    worklist = deque()
    for v in trans_G.vertices():
        mapping[v] = bottom
        worklist.append(v)

    while worklist:
        node = worklist.pop()
        # Combines live_before of all blocks which the current node jumps to
        input = reduce(join, [mapping[v] for v in G.adjacent(node)], bottom)
        output = transfer(node, input)
        if output != mapping[node]:
            mapping[node] = output
            worklist.extend(trans_G.adjacent(node))

    return mapping
