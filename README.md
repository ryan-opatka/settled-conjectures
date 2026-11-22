# Conjectures settled in Lean

Open conjectures settled by proofs that the Lean 4 kernel has checked, using Mathlib. There is
no `sorry` and no added axiom: each main theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.

| Conjecture | Result | Theorem | Where |
| --- | --- | --- | --- |
| Z.-W. Sun, *Problems on combinatorial properties of primes* (arXiv:1402.6641), Conjecture 4.6. Also part (i) of the conjecture in OEIS A235343. | False. It fails at n = 267497. | `Sun46.conjecture_false` | [`Sun46/`](Sun46/README.md) |

## Sun's Conjecture 4.6

Let φ be Euler's totient function and q(m) the number of partitions of m into distinct
parts. Sun conjectured in 2014 that for every n ≥ 60 there is a positive integer k < n such
that m − 1, m + 1 and q(m) + 1 are all prime, where m = φ(k) + φ(n − k)/4. For n = 267497
there is no such k. The proof, the checks made outside Lean, and what is known about novelty
are described in [`Sun46/README.md`](Sun46/README.md).

## Build

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
- `scripts/` — Python and PARI/GP programs: the search for the counterexample, four checks of
  it that share no code, the comparison with Sun's OEIS tables, and the generators of the
  data files. They need `gmpy2`, `sympy`, `numpy`, `python-flint` and `cypari`.

## Licence

Apache License 2.0, see [`LICENSE`](LICENSE). This matches Lean and Mathlib.

## Provenance

The counterexample was found and the proof was written by Claude, an AI model made by
Anthropic, working with a human collaborator. The Lean kernel checks the proof independently
of both. Nothing here has been peer reviewed.
