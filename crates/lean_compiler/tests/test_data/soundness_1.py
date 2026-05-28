from snark_lib import *


def main():
    p = 0
    n = p[0]
    sum_range = p[1]
    x = p[2]
    prod = p[3]

    assert n == 5

    s: Mut = 0
    for i in range(0, 5):
        s = s + i
    assert s == sum_range

    assert mul(x, x) == prod
    return


def mul(a, b):
    return a * b
