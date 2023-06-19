from x86_ast import Reg

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

NUM_REG_ALLOCATION = {
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

REG_NUM_ALLOCATION = {
    # Caller-saved
    "rcx": 0,
    "rdx": 1,
    "rsi": 2,
    "rdi": 3,
    "r8": 4,
    "r9": 5,
    "r10": 6,
    # Callee-saved
    "rbx": 7,
    "r12": 8,
    "r13": 9,
    "r14": 10,
}
