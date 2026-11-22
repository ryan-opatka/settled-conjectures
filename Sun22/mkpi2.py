# pi at chunk boundaries up to a given bound
import sys, primecountpy as pc
need = int(sys.argv[1]); TC = (1 << 22) * 2730; nch = need // (6 * TC) + 1
with open(sys.argv[2], 'w') as f:
    for c in range(nch + 1): f.write(f'{6 * TC * c} {pc.prime_pi(6 * TC * c)}\n')
print('chunks', nch)
