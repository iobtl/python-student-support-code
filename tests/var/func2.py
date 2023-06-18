def tail_sum(n: int, r: int) -> int:
    if n == 0:
        return r
    else:
        return tail_sum(n - 1, n + r)


print(tail_sum(3, 0) + 3)
