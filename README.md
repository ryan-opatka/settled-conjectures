# Settled conjectures

Open conjectures settled with machine help. Each entry says how it was checked: by a proof
that the Lean 4 kernel has verified, or by computation.

| Conjecture | Result | How it was checked | Where |
| --- | --- | --- | --- |
| Z.-W. Sun, *Problems on combinatorial properties of primes* (arXiv:1402.6641), Conjecture 4.6. Also part (i) of the conjecture in OEIS A235343. | False. It fails at n = 267497. | Lean 4 proof, `Sun46.conjecture_false`. No `sorry`; depends only on `propext`, `Classical.choice`, `Quot.sound`. | [`Sun46/`](Sun46/README.md) |
| Same paper, Conjecture 2.2(i). Also the conjecture in OEIS A237597. | False. It fails at n = 778368, and for no other n ≤ 10^6. | Computation, by two programs that share no code. Not a Lean proof. | [`Sun22/`](Sun22/README.md) |
| Same paper, the conjecture in the remark after Conjecture 2.4. Also Conjecture (ii) of OEIS A237598. | False. It fails at n = 1471. | Computation, by three programs. Not a Lean proof. | [`Sun22/`](Sun22/README.md) |
| Z.-W. Sun, the conjecture in OEIS A234361 (2013). | False. It fails at n = 27135, the smallest counterexample. | Computation, by two programs that share no code. Not a Lean proof. | [`SunOEIS/`](SunOEIS/README.md) |
| Z.-W. Sun, Conjecture (ii) in OEIS A234451 (2013), in both of its forms. | False. The first form fails at n = 62191, the second at n = 83843. | Computation: every exponent that occurs was tested directly. Not a Lean proof. | [`SunOEIS/`](SunOEIS/README.md) |

Checked further but not settled: Sun's 1680-conjecture (OEIS A280831) holds for every number
below 10^10, a hundred times further than had been verified; see [`Sun1680/`](Sun1680/README.md).

## Sun's Conjecture 4.6

Let φ be Euler's totient function and q(m) the number of partitions of m into distinct
parts. Sun conjectured in 2014 that for every n ≥ 60 there is a positive integer k < n such
that m − 1, m + 1 and q(m) + 1 are all prime, where m = φ(k) + φ(n − k)/4. For n = 267497
there is no such k. The proof, the checks made outside Lean, and what is known about novelty
are described in [`Sun46/README.md`](Sun46/README.md).

## Sun's Conjecture 2.2(i)

Let π(x) be the number of primes up to x and p_n the n-th prime. Sun conjectured in 2014
that for every positive integer n there is a positive integer k < p_n with π(kn) divisible
by n. For n = 778368 there is none: the least such k is 11864258, and p_n = 11842709. The
computation and its checks are described in [`Sun22/README.md`](Sun22/README.md), together
with a smaller counterexample (n = 1471) to a related conjecture stated in a remark of the
paper, and the ranges in which some neighbouring conjectures were checked and held.

## Build

The Lean proof of the counterexample to Conjecture 4.6:


Install [elan](https://github.com/leanprover/elan), then in this directory:

```bash
lake exe cache get
```

```bash
lake build
```

The toolchain is pinned in `lean-toolchain` (Lean 4.36.0-rc2 with the matching Mathlib).
The build prints

```
'Sun46.conjecture_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The proof takes about nine minutes on four cores, with a peak of about 7.5 GB of memory. The
first run also spends a few minutes reading Mathlib's cache.

## Layout

- `Sun46/` — the Lean proof of the counterexample to Sun's Conjecture 4.6, and its write-up.
  `Data.lean`, `Table.lean` and `Chunks/` are generated; nothing in them is trusted.
- `Sun22/` — the computations for Conjecture 2.2(i) and its neighbours, and their write-up:
  C programs (OpenMP) and Python programs that need `primecountpy`, `gmpy2`, `numpy` and,
  for one of them, `python-flint`.
- `SunOEIS/` — computations for Sun's exponential conjectures in OEIS A234361 and A234451, and
  their write-up. Python programs that need `gmpy2`, `numpy`, `sympy` and `cypari`.
- `Sun1680/` — the verification of Sun's 1680-conjecture up to 10^10: a C program (OpenMP) and
  its output.
- `scripts/` — for Conjecture 4.6. Python and PARI/GP programs: the search for the counterexample, four checks of
  it that share no code, the comparison with Sun's OEIS tables, and the generators of the
  data files. They need `gmpy2`, `sympy`, `numpy`, `python-flint` and `cypari`.

## Licence

Apache License 2.0, see [`LICENSE`](LICENSE). This matches Lean and Mathlib.

## Provenance

The counterexamples were found, and the proof and the programs written, by Claude, an AI
model made by Anthropic, working with a human collaborator. The Lean kernel checks the proof
of the first independently of both; the others rest on the computations described.
Nothing here has been peer reviewed.
