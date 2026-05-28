from snark_lib import *


def main():
    p = 0
    seed = p[0]
    last_write = p[1]
    match_tally = p[2]
    alt = p[3]

    counter: Mut = 0
    for i in range(0, 4):
        counter = 2 * i + 1
    assert counter == last_write

    acc: Mut = seed
    for i in range(0, 4):
        match i:
            case 0:
                acc = acc + 1
            case 1:
                acc = acc + 3
            case 2:
                acc = acc + 5
            case 3:
                acc = acc + 7
    assert acc == match_tally

    chosen: Imm
    if seed == 0:
        chosen = 0
    else:
        chosen = seed * 2
    assert chosen == alt
    return
