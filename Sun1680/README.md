# Sun's 1680-conjecture holds up to 10^10

A verification, not a solution. No counterexample was found.

## The conjecture

Z.-W. Sun (OEIS A280831; 1680 RMB offered in 2020 "for the first complete solution"): every
natural number n can be written as x² + y² + z² + w² with x, y, z, w nonnegative integers
such that x⁴ + 1680·y³·z is a square. Numbers that are sums of three squares satisfy it
trivially (take z = 0), and the form 4^k(8m + 7) reduces to 8m + 7 by scaling. So the
conjecture is equivalent to a(m) > 0 for all m ≥ 0, where a(m) is the number of ways to
write 8m + 7 = x² + y² + z² + w² with x, y, z, w positive and x⁴ + 1680y³z a square.
Qing-Hu Hou had verified it for n up to 10^8.

## Result

**a(m) > 0 for every m with 8m + 7 < 10^10.** The smallest values of a(m) grow:

| m | smallest a(m) | where | m with a(m) ≤ 10 |
| --- | --- | --- | --- |
| 10^6 to 10^7 | 2 | m = 1102990 | 3893 |
| 10^7 to 10^8 | 5 | m = 11935882 | 888 |
| 10^8 to 10^9 | 5 | m = 170853403 | 54 |
| 10^9 to 1.25·10^9 | 11 | m = 1019677918 | 0 |

The last m with a(m) = 1 is 121765. Nothing here suggests a failure further out.

## Method

Searching over x is hopeless at this size. Instead `c1680.c` lists every
(x, y, z) with x⁴ + 1680y³z = t² directly. Put u = t − x², v = t + x² and M = 1680y³, so that
uv = Mz. With M1 = gcd(u, M) and M2 = M/M1 we get u = M1·u′, v = M2·v′, u′v′ = z,
gcd(u′, M2) = 1 and M2·v′ − M1·u′ = 2x². So for each y and each pair (u′, v′) with
u′v′ ≤ √N, the program looks among the divisors M1 of M for those that make M2·v′ − M1·u′
twice a square. Each solution arises exactly once. There are 29542491 of them below 10^10,
of which 4957018 can occur for a number of the form 8m + 7.

## Checks

- For N = 3·10^5 the list equals the one found by brute force over all (x, y, z)
  (`brute_triples.py`): 21005 triples, none missing, none extra, none repeated.
- The counts reproduce the first terms of A280831.
- Running in pieces over ranges of y gives the same counts as a single run (N = 10^7).

The run took about five hours of processor time. Its output is `count_1e10.log`.
