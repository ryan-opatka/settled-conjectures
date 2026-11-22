# Sun's Conjecture 2.2(i) on π(kn) modulo n is false

A computation, not a Lean proof. The counterexample is n = 778368.

## The conjecture

Let π(x) be the number of primes not exceeding x and let p_n be the n-th prime.

Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641 (v12, 2016);
in *Number Theory: Plowing and Starring through High Wave Forms*, World Scientific, 2015,
pp. 169–187:

> **Conjecture 2.2** (2014-02-10). (i) For any positive integer n, there is a positive
> integer k < p_n such that π(kn) ≡ 0 (mod n).
> (ii) For each positive integer n, the set {π(kn) : k = 1, …, 2p_n} contains a complete
> system of residues modulo n.

Part (i) is also the conjecture in OEIS A237597, where a(n) is the number of such k, and
A237614 lists the least k. The paper offers a prize of 1000 RMB "for the first complete
solution to any one of the 60 conjectures". Sun's tables in the OEIS stop at n = 2500
(A237597) and n = 10000 (A237614); the paper gives no range of verification.

## The result

**For n = 778368 there is no positive integer k < p_n with π(kn) divisible by n.**
Here p_n = 11842709, so k runs up to 11842708 and kn up to 9217984940544.

It is the only such n up to 10^6, so it is the smallest counterexample.

Two computations that share no code agree on this.

1. A sieve of all primes below 1.55·10^13 (`fast22.c`), which counts the
   suitable k for every n ≤ 10^6 at once, finds none for n = 778368.
2. Without any sieve of ours (`verify_hit.py`): n divides π(kn) exactly when
   kn lies in [p_{jn}, p_{jn+1}) for some j. Since π(n(p_n − 1)) = 410995·n + 82745, only
   j = 1, …, 410995 matter. For each of them p_{jn} was computed with primecount and
   p_{jn+1} with GMP, and no multiple of n lies between the two.

The nearest misses are k = 728129 and k = 1843479, where π(kn) is 27982·n + 1 and
68399·n + 1. The least k with n | π(kn) is 11864258, where π(kn) = 411717·n. That is
21549 more than the bound k < p_n allows, about 0.18% too far.

## How it was found

n divides π(kn) exactly when π(kn) = jn for some j, that is, when the multiple kn lies in
the gap [p_{jn}, p_{jn+1}) that starts at the prime of index jn. So a(n) is the number of
multiples of n, below n·p_n, that fall in one of those gaps. There are about n/2 gaps to
look at, each of length about log(n²) ≈ 2 log n, so the expected number of hits is about
p_n/n ≈ log n + log log n − 1, and the chance of none is about e^(−p_n/n). Summed over n
this diverges, slowly: about one n per decade should fail. For n ≤ 10^5 the number of n
with exactly one, two or three such k is what this model predicts (31, 104, 335 against
25, 103, 315), and it predicts 0.48 failures between 10^5 and 10^6. There is one.

`fast22.c` walks through all primes below 1.55·10^13 once, in parallel,
and counts the hits for every n ≤ 10^6 together. It took 88 minutes on four cores.

To repeat it (needs `gcc` with OpenMP and the Python package `primecountpy`):

```bash
gcc -O2 -march=native -fopenmp -o fast22 fast22.c -lm
```

```bash
python3 mkpi.py 1000000 pi.txt
```

```bash
./fast22 1000000 pi.txt out 4
```

`a237597_1000000.u8` holds the result: byte n is the number of suitable k for n. To repeat
the independent check of n = 778368, which took 69 minutes on four cores
(`verify_778368.log` is its output):

```bash
python3 verify_hit.py 778368 4
```

## Checks

- **The sieve.** The number line is cut into 226 pieces. For every piece the number of
  primes found equals π(end) − π(start) as computed by primecount (Kim Walisch's
  implementation of the Meissel–Lehmer method), which shares no code with the sieve.
- **Sun's data.** The counts agree with all 2500 terms of his table of A237597.
- **Other programs.** For n ≤ 3000 the counts equal those of a brute-force program that
  computes π(kn) for every k from a table (`small22.py`). For n ≤ 10^5 they equal those of
  a second C program with a different sieve (`c22i.c`).
- **The counterexample itself** was recomputed without the sieve, as described above. The
  same independent program gives the sieve's counts for n = 759, 2552 and 4800.
- **Minimality** rests on the sieve program alone: for every other n ≤ 10^6 it found at
  least one k.

## Other things tested on the way

Same paper, same method. None of these is a counterexample to a numbered conjecture.

| Statement | Result |
| --- | --- |
| 2.2(i), all other n ≤ 10^6 | holds |
| 2.2(ii): {π(kn) : k ≤ 2p_n} covers all residues mod n | holds for n ≤ 10^5 (`fast22ii.c`) |
| 2.14(i): {π(k²) : k ≤ 2p_{n+1} − 3} covers all residues mod n | holds for n ≤ 146868; n = 131596 needs 99.1% of the range (`c214.c`) |
| 2.4(i): π(kn) is a square for some k < p_n | holds for n ≤ 10^5 (`post24.py`) |
| 2.6(ii): π(π(kn)) is a square for some k ≤ n, and triangular for some k ≤ (n+1)/2 | holds for n ≤ 10^5 (`c26.py`) |
| 4.5: n = k + m with p_k + φ(m) and q(p_k + φ(m)) ∓ 1 prime | holds for n ≤ 8818, with exactly the exceptions Sun lists (`c45.py`) |
| Remark after 2.4, and Conjecture (ii) of A237598: for n > 9 some k < p_n/2 has π(kn) triangular | **false at n = 1471** (`tri1471.py`) |

For n = 1471: p_n = 12301, and the k < p_n with π(1471k) triangular are 6321, 8929, 9904,
11393 and 11929, all above p_n/2. Three computations agree (a sieve, primecount, PARI/GP).
The other n ≤ 10^5 without such a k are 1, 4 and 9, which is why Sun wrote n > 9. This
statement is in a remark, not among the 60 numbered conjectures.

## Status

- **Not proved in Lean.** A formal proof would need the number of primes below 9·10^12 at
  about 400000 places, which is out of reach for the kernel. The claim rests on the
  computations above.
- **Not reviewed** by a person.
- **Novelty.** On 22 November 2026 the OEIS entries A237597 and A237614 (both last edited
  in February 2014) and A237598 state the conjectures with no counterexample noted. The
  OEIS Open results and `F8Labs-ai/sun_conjectures` do not include them.
- **The prize** is Sun's to award.
