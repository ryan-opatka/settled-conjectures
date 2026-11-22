\\ Sun's Conjecture 4.6 (arXiv:1402.6641), checked at one n with PARI/GP.
\\ Usage in gp:   \r verify46.gp      then      report(267497)
\\ q(m) = number of partitions of m into distinct parts, from Gauss's identity
\\   q(m) = sum over triangular numbers t <= m with t = m (mod 2) of numbpart((m-t)/2).
q(m) = { my(s = 0, j = 0, t = 0); while(t <= m, if((m - t) % 2 == 0, s += numbpart((m - t)/2)); j++; t = j*(j+1)/2); s };
\\ returns [ number of k with m integral and m-1, m+1 prime,
\\           number of distinct such m,
\\           number of those m where 2^(q(m)) != 1 mod q(m)+1  (so q(m)+1 is composite),
\\           list of [k, m] with q(m)+1 passing that test ]
check(n) = {
  my(W = List(), M = Map(), e, m, N, c = 0, comp = 0, v);
  for(k = 1, n - 1,
    e = eulerphi(n - k);
    if(e % 4, next);
    m = eulerphi(k) + e/4;
    if(!isprime(m - 1) || !isprime(m + 1), next);
    c++;
    if(!mapisdefined(M, m),
      N = q(m) + 1;
      v = (N > 2 && lift(Mod(2, N)^(N - 1)) != 1);
      mapput(M, m, v); if(v, comp++));
    if(!mapget(M, m), listput(W, [k, m])));
  [c, #M, comp, Vec(W)]
};
report(n) = {
  my(r = check(n));
  printf("n = %d: %d values of k give an integer m with m-1 and m+1 prime (%d distinct m); q(m)+1 fails the Fermat test to base 2 for %d of them.\n", n, r[1], r[2], r[3]);
  if(#r[4] == 0, print("NO k works: Conjecture 4.6 fails at n = ", n), print("candidates [k, m] with q(m)+1 a base-2 probable prime: ", r[4]));
  r
};
