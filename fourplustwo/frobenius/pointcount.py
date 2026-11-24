"""Independent checks from point counts at p:
   #T(F_p) = 1 + p + p^2 + p^3 - Tr(Frob | H^3(T)),  T: u^3 + H = 0 in P(1,1,1,1,2);
   the quadratic twist in (c,d) gives Tr(sigma Frob), hence the traces on the sigma-even and sigma-odd parts."""
import sys, numpy as np
p = int(sys.argv[1]); k = 5*pow(7, -1, p) % p
eps = next(e for e in range(2, p) if pow(e, (p-1)//2, p) == p-1)      # a non-residue
r = np.arange(p, dtype=np.int64)
a, b, c, d = np.meshgrid(r, r, r, r, indexing='ij')
tab = lambda n: np.array([pow(int(t), n, p) for t in range(p)], dtype=np.int64)
P5, P6 = tab(5), tab(6)
def trace(e):          # e = 1: T itself; e = eps: twist (c,d) -> sqrt(eps) (c,d)
    e2, e3 = e*e % p, pow(e, 3, p)
    H = (P6[a] + P6[b] + k*P5[a]*b + 2*k*a*P5[b] + e3*(P6[c] + P6[d] + k*P5[c]*d + 3*k*c*P5[d])
         + k*a*b*c*d % p*(e*a*a + 2*e2*c*c)) % p
    cubes = np.zeros(p, dtype=np.int64)
    for u in range(p): cubes[(-pow(u, 3, p)) % p] += 1
    N_aff = int(cubes[H].sum()); assert (N_aff - 1) % (p - 1) == 0
    return 1 + p + p*p + p**3 - (N_aff - 1)//(p - 1)
t1, t2 = trace(1), trace(eps)
print(f'p={p}: Tr(Frob | H^3) = {t1}, twisted = {t2}; sigma-even part {(t1+t2)//2}, sigma-odd part {(t1-t2)//2}')
