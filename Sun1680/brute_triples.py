# All (x, y, z) with x, y, z >= 1, x^2 + y^2 + z^2 < N and x^4 + 1680 y^3 z a perfect square, by brute force.
import sys, math, numpy as np
N = int(sys.argv[1]); R = int(math.isqrt(N)); out = []
for y in range(1, R + 1):
    for x in range(1, R + 1):
        rem = N - x * x - y * y
        if rem < 2: break
        z = np.arange(1, int(math.isqrt(rem - 1)) + 1, dtype=np.int64)
        v = x ** 4 + 1680 * y ** 3 * z
        r = np.sqrt(v.astype(np.float64)).astype(np.int64); r = np.where((r + 1) * (r + 1) <= v, r + 1, r); r = np.where(r * r > v, r - 1, r)
        for zg in z[r * r == v].tolist(): out.append((x, y, zg))
np.save(sys.argv[2], np.array(out, dtype=np.int64)); print(len(out), 'triples')
