# Sun's exponential conjectures in the OEIS: three that fail

Computations, not Lean proofs. No prize is attached to any of these.

| OEIS entry | Sun's claim | Fails at |
| --- | --- | --- |
| A234361 | for n > 7 some 0 < k < n has 2^(φ(k)/2)·3^(φ(n−k)/4) + 1 prime | n = 27135, the smallest |
| A234451 (ii), first form | for n > 25, n = k + m with 3·2^(φ(k)/2 + φ(m)/8) + 1 prime | n = 62191 |
| A234451 (ii), second form | for n > 38, the same with φ(m)/12 | n = 83843 |

## Why these should fail

Many of Z.-W. Sun's conjectures from 2013–2014 say that for every large n some 0 < k < n makes
an expression in φ(k) and φ(n − k) prime. When the expression is exponential in those values,
the set of exponents that give a prime is so thin that the expected number of suitable k does
not grow with n. In Sun's own tables the average stays near 10 from one third of the table to
the next. So each of these conjectures should fail at some n; the question is only where.

## A234451, Conjecture (ii)

**OEIS A234451, Conjecture (ii).** Sun: every n > 25 can be written as k + m (k, m > 0) with
3·2^(φ(k)/2 + φ(m)/8) + 1 prime, and for n > 38 the same holds with φ(m)/12 in place of φ(m)/8.
He reports checking n ≤ 50000.

| Form | Fails at | Exponents that occur | Result |
| --- | --- | --- | --- |
| 3·2^e + 1, e = φ(k)/2 + φ(m)/8 | n = 62191 | 46978 values of k give an integer e; 17161 distinct e, from 1743 to 31086 | 3·2^e + 1 is composite for every one |
| 3·2^e + 1, e = φ(k)/2 + φ(m)/12 | n = 83843 | 55569 values of k; 21452 distinct e, from 1538 to 41897 | composite for every one |

Each exponent was tested directly with GMP (`verify_exp.py`); a failed strong
probable-prime test proves compositeness, so the result does not depend on any table of known
primes. The numbers agree with the list of e with 3·2^e + 1 prime in OEIS A002253: according
to that list these are the smallest failures, and there are 128 failures of the first form and
10 of the second up to n = 2·10^6 (`e2scan.py`).

The reading of each statement was checked against Sun: the program reproduces the first terms
of A234451 and A234504, and the n without a representation below his thresholds are exactly
the ones his thresholds exclude (`e2brute.py`).

## Other statements in the same entries

With the tabulated lists (not verified by us beyond the tables): the forms 2^e + 3, 2^e − 3 and
3·2^e − 1 of A234451 and both parts of A236358 (2·3^e ± 1) have no failure in the range the
lists cover (n up to 2·10^6, or 4·10^5 for 3·2^e − 1).

## A234361: two exponentials

Sun: a(n) = #{0 < k < n : 2^(φ(k)/2)·3^(φ(n−k)/4) + 1 is prime} is positive for all n > 7. His
table goes to n = 5000.

**a(27135) = 0.** For n = 27135 = 3^4·5·67 there are 24770 values of k for which both
exponents are integers, giving 24327 distinct pairs of exponents and numbers of up to about
13565 bits. None is prime. Two programs agree: `e1scan.py` (totients by sieve, GMP for
primality, after removing numbers with a prime factor below 60000) and `indep_A234361.py`
(totients from SymPy, PARI's Baillie–PSW test), which share no code. Both reproduce Sun's table
where tested (all of n ≤ 400; n = 1000 and n = 4999).

It is the smallest counterexample: Sun's table has no zero for 7 < n ≤ 5000, and the scan
found a prime for every n from 5001 to 27134.

In Sun's table the average of a(n) is 9.6 in the last third and 10.3 in the middle third. A
sample of twelve n between 18000 and 22000 gave an average of 9.0. With an average near 9
about one n in ten thousand should have none, so a failure near 27000 is what one expects.

## The rest of the family

Same structure, same flat averages in Sun's tables (about 10 to 12). Ranges scanned so far, in
every case with a prime found for each n:

| OEIS entry | Expression | Sun's table | Scanned with no failure |
| --- | --- | --- | --- |
| A234347 | 3^k + 3^(φ(n−k)/2) − 1 | n ≤ 3000 | to n = 21000 |
| A234337 | 4^k + 2^φ(n−k) − 1 | n ≤ 4000 | to n = 17000 |
| A234344 | 2^(φ(k)/2) + 3^(φ(n−k)/2) | n ≤ 7000 | to n = 35000 |
| A234309 | 2^φ(k) + 2^φ(n−k) − 1 | n ≤ 8000 | to n = 30000 |

Two relatives were refuted earlier by others: A234399 at n = 5962 (J. Yuen, 2024) and A234360
at n = 1408 (T. Adamczewski, 2026).

## Not verified

A234504 (2^(φ(k) + φ(m)/4) − 5 prime, n > 10): the tabulated list A059608 gives a first failure
at n = 167665. The direct check of the 61838 exponents that occur did not finish in the time
available, so this is a prediction and not a result.
