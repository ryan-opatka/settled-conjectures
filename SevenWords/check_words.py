#!/usr/bin/env python3
"""Plain-integer check of the classification: which words occur in every orbit above d."""
from itertools import product
def T(d, n): return n // 2 if n % 2 == 0 else (3 * n + d) // 2
def cycle_word(d, n):
    w, x = '', n
    while True:
        w += 'C' if x % 2 else 'F'
        x = T(d, x)
        if x == n: return w
def factors(w, L):
    ww = w * (L // len(w) + 2)
    return {ww[i:i + L] for i in range(len(w))}
c19 = [19, 31, 49, 76, 38]; c23 = [23, 37, 58, 29, 46]
for c in (c19, c23):
    assert all(T(5, c[i]) == c[(i + 1) % 5] for i in range(5)) and min(c) > 5
w19, w23 = cycle_word(5, 19), cycle_word(5, 23)
print('words', w19, w23)
seven = {'C', 'F', 'CC', 'CF', 'FC', 'CCF', 'FCC'}
for L in range(1, 7):
    for t in product('CF', repeat=L):
        w = ''.join(t)
        on_both = w in factors(w19, L) and w in factors(w23, L)
        assert on_both == (w in seven), w
print('words of length <= 6 on both T_5 cycles are exactly the seven: ok')
# The seven do occur in every eventually periodic orbit above d, small survey
import sys
bad = 0; cycles = 0
for d in range(1, 200, 2):
    seen = set()
    for n in range(1, 3000):
        x = n; path = {}
        while x not in path and x < 10**12:
            path[x] = len(path); x = T(d, x)
        if x not in path: continue
        cyc = [y for y in path if path[y] >= path[x]]
        m = min(cyc)
        if m in seen or m <= d: continue
        seen.add(m); cycles += 1
        w = cycle_word(d, m)
        for s in seven:
            if s not in factors(w, len(s)): bad += 1; print('MISSING', d, m, w, s)
print('cycles above d surveyed:', cycles, 'violations of the seven:', bad)
# Proposition 6 exception: d = 13, 8-cycle through 283, all terms = 13 or 26 mod 5
x = 283; c = []
for _ in range(8): c.append(x); x = T(13, x)
assert x == 283 and all(y % 5 in (13 % 5, 26 % 5) for y in c) and 13 not in c
print('283-cycle of T_13:', c, [y % 5 for y in c])
# the two families, small members: word CCF(CF)^s and C^a FF (CCCFF)^s
from fractions import Fraction
def cyc_from_word(p):
    k, o = len(p), p.count('C'); d = 2**k - 3**o
    c = 0
    for j, ch in enumerate(p):
        if ch == 'C': c += 2**j * 3**(p[j+1:].count('C'))
    return d, c
for s in range(0, 6):
    p = 'CCF' + 'CF' * s
    d, c = cyc_from_word(p)
    x = c; ok = True; w = ''
    for _ in range(len(p)):
        ok &= x > d; w += 'C' if x % 2 else 'F'; x = T(d, x)
    assert x == c and ok and w == p and d == 2**(2*s+3) - 3**(s+2), (s, d, c)
for a in range(3, 7):
    for s in range(0, 4):
        p = 'C' * a + 'FF' + 'CCCFF' * s
        d, c = cyc_from_word(p)
        x = c; ok = True; w = ''
        for _ in range(len(p)):
            ok &= x > d; w += 'C' if x % 2 else 'F'; x = T(d, x)
        assert x == c and ok and w == p and d == 2**(a+2+5*s) - 3**(a+3*s), (a, s)
print('family members are cycles above d with the stated words: ok')
