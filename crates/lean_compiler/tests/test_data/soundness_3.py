from snark_lib import *


def main():
    p = 0
    seed = p[0]
    sum_expected = p[1]
    prod_expected = p[2]
    w = p[3]

    arr = Array(4)
    for i in unroll(0, 4):
        arr[i] = seed + i

    s: Mut = 0
    for i in range(0, 4):
        s = s + arr[i]
    assert s == sum_expected

    prod: Mut = 1
    for i in unroll(0, 4):
        prod = times(prod, arr[i])
    assert prod == prod_expected

    assert w == seed + 1
    return


@inline
def times(a, b):
    return a * b
