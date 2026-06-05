# ZK leanVM: high level ideas

## PCS

Something inspired by [VEIL](https://eprint.iacr.org/2026/683.pdf) ?

## Logup / AIR sumcheck

## Sumcheck messages (i.e. small polynomails sent at each round of a sumcheck)

- using masks as in [Libra](https://eprint.iacr.org/2019/317) ?
- Maybe by introducing a 4-th table, full of random data, always bigger than the other tables? (playing indirectly the role of a big mask)
- proving that the 'structured-randomness' (see below) is enough?

## Column evaluations

At two steps of the protocols (logup / AIR), the prover send directly the evluations of some of the columns (potentially 'shifted') at some point. Maximum of 3 evaluations per column.

One idea would be to 'padd' the end of each column with a few random rows, but we are constrained: our columns should respect the AIR constraints / logup bus balancing. We can still happen some structured random padding:
- poseidon table: take a random input, hash it
- extension table: compute dot products over random inputs
- execution table: feel memory with random data, and perform conditional execution based on this

Each columns leaks at most n = 3 * size(Fq) = 3 * 155 bits = 465 bits of information.
Conjecture: It's enough, for each column that can take up to 2^k different values (typically k=1 for boolean columns), to have, within the 'structured random' padding, at least n / k rows, where the values of this column are chosen uniformly at random, and the other columns values are set such that AIR constraints are respected. 