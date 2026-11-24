"""Analysis of the output of the patched ToricControlledReduction driver (coset_frob) for the
sigma-odd part of H^3(T), T: u^3 + H = 0, split by the deck character.

  piece 1 = exponents with c+d odd, u = 1 mod 3   Hodge (h30,h21,h12,h03) = (0,32,16,0)
  piece 2 = exponents with c+d odd, u = 2 mod 3   Hodge (0,16,32,0), dual to piece 1

Files data/c{r}_p{p}_N{k}.txt: 'row j m : v' = coordinates of Frob(basis element j, pole order m).
Columns of pole order 3 are computed mod p^2 (N2) or p^3 (N3); those of pole order 2 only in N3.

For each prime: the slope-1 polynomial of piece r mod p is the characteristic polynomial of the
(pole 3, pole 3) block of Frob/p.  By duality the slope-1 polynomial of piece 2 has the same
p-adic factor degrees as the slope-2 part of piece 1.
"""
import sys, os
from flint import nmod_mat, fmpz_mat
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data')
POINTCOUNT = {19: 133, 31: -155, 67: 134}        # trace on the sigma-odd part, from pointcount.py
# kmehltretter82's eigen-traces a + b*zeta on V_zeta (discussion 120, 2026-11-21); the sum over both pieces is 2a - b
EIGENTRACE = {19: (76, 19), 31: (-93, -31), 37: (-296, -185), 43: (215, 215), 61: (-61, -122)}

def load(r, p, tag):
    d = {}; rows = {}
    for line in open(os.path.join(D, f'c{r}_p{p}_{tag}.txt')):
        if line.startswith('row'):
            h, v = line.split(':'); _, i, m = h.split(); rows[int(i)] = (int(m), [int(x) for x in v.split()])
        else:
            k, _, v = line.strip().partition(' '); d[k] = v.strip()
    xin = [int(x) for x in d['X_in_Y'].split()]
    return d, rows, xin

def unit_poly(r, p, tag):
    d, rows, xin = load(r, p, tag)
    n = len(xin)
    idx3 = [j for j in range(n) if rows[j][0] == 3]
    xs = set(xin)
    assert all(x % p**2 == 0 for j in idx3 for c, x in enumerate(rows[j][1]) if c not in xs), 'not in H^3(T)'
    assert all(x % p == 0 for j in idx3 for x in rows[j][1]), 'pole-3 column not divisible by p'
    B = nmod_mat(len(idx3), len(idx3), [(rows[j][1][xin[i]] // p) % p for i in idx3 for j in idx3], p)
    return d['piece_hodge'], B.charpoly(), int(sum(B[i, i] for i in range(len(idx3))))

def subset_sums(ds):
    s = {0}
    for d in ds: s |= {x + d for x in s}
    return s

def main():
    primes = sorted({int(f.split('_p')[1].split('_')[0]) for f in os.listdir(D) if f.endswith('_N2.txt')})
    S1 = S2 = None
    print('p-adic factor degrees of the characteristic polynomial of Frobenius on piece 1 (48 = 16 + 32)')
    for p in primes:
        out = []; tot = 0
        for r in (1, 2):
            h, cp, tr = unit_poly(r, p, 'N2')
            fac = cp.factor()[1]
            assert int(cp[0]) != 0, 'not ordinary'
            sq = all(e == 1 for f, e in fac)
            out.append((sorted(f.degree() for f, e in fac for _ in range(e)), sq))
            tot += tr
        if out[0][1]: S1 = subset_sums(out[0][0]) if S1 is None else S1 & subset_sums(out[0][0])
        if out[1][1]: S2 = subset_sums(out[1][0]) if S2 is None else S2 & subset_sums(out[1][0])
        chk = ''
        if p in POINTCOUNT:
            chk = '   trace check vs point count: ' + ('OK' if (p*tot - POINTCOUNT[p]) % p**2 == 0 else 'MISMATCH')
        note = lambda o: '' if o[1] else ' (not squarefree mod p; not used)'
        print(f'  p = {p:3d}: slope 1: {out[0][0]}{note(out[0])}   slope 2: {out[1][0]}{note(out[1])}{chk}')
        print(f'           possible (slope-1 rank, slope-2 rank) of a sub-object so far: {sorted(S1)} x {sorted(S2)}')
    # full matrices mod p^3 where available
    for p in primes:
        if not os.path.exists(os.path.join(D, f'c1_p{p}_N3.txt')): continue
        tot = 0
        for r in (1, 2):
            d, rows, xin = load(r, p, 'N3'); n = len(xin); xs = set(xin)
            assert all(x % p**3 == 0 for j in range(n) for c, x in enumerate(rows[j][1]) if c not in xs)
            assert all(x % p**(4 - rows[j][0]) == 0 for j in range(n) for x in rows[j][1]), 'Hodge divisibility'
            tot += sum(rows[j][1][xin[j]] for j in range(n))
            # the slope-1 polynomial agrees with the N2 run
            idx3 = [j for j in range(n) if rows[j][0] == 3]
            B = nmod_mat(len(idx3), len(idx3), [(rows[j][1][xin[i]] // p) % p for i in idx3 for j in idx3], p)
            assert B.charpoly() == unit_poly(r, p, 'N2')[1]
        t = tot % p**3
        t = t if t < p**3 // 2 else t - p**3
        et = EIGENTRACE.get(p)
        print(f'  p = {p}: full 96-dimensional trace mod p^3 = {t}; point count {POINTCOUNT.get(p)}; '
              f'from the posted eigen-traces {None if et is None else 2*et[0] - et[1]}')

if __name__ == '__main__':
    main()


# ---------------------------------------------------------------------------------------------
# Powers of Frobenius.  A sub-object defined over a number field is only stable under a power
# Frob^f.  The factor degrees of the characteristic polynomial of Frob^f over Q_p are the same as
# for Frob unless sigma^k(alpha)/alpha is a root of unity for two distinct conjugate roots.  For a
# unit root alpha in the unramified extension of degree d write alpha = teich(alpha)(1 + p eps);
# then alpha^(p^d - 1) = 1 - p eps mod p^2, and sigma^k(alpha)/alpha is a root of unity only if
# eps mod p is fixed by sigma^k.  So it is enough that eps mod p generates F_{p^d}.
# Needs the unit-root polynomial mod p^2, i.e. all columns of Frob mod p^3 (the N3 runs).
from flint import nmod_poly, fmpz_poly

def unit_factors_mod_p2(r, p):
    d, rows, xin = load(r, p, 'N3'); n = len(xin)
    M = fmpz_mat(n, n, [(rows[j][1][xin[i]] // p) % p**2 for i in range(n) for j in range(n)])   # Frob/p mod p^2
    chi = [int(c) % p**2 for c in M.charpoly().coeffs()]
    chi_p = nmod_poly(chi, p)
    out = []
    for h, e in chi_p.factor()[1]:
        if h.degree() == 1 and int(h[0]) == 0: continue          # the factor T (slope > 0 part)
        if e != 1: return None                                   # not squarefree mod p
        c = chi_p // h                                           # coprime to h
        # one Hensel step: (h + p h1)(c + p c1) = chi mod p^2,  h1 = e c^(-1) mod h
        prod = fmpz_poly([int(x) for x in h.coeffs()]) * fmpz_poly([int(x) for x in c.coeffs()])
        diff = [(a - int(prod[i])) for i, a in enumerate(chi)]
        assert all(x % p == 0 for x in diff)
        ee = nmod_poly([(x // p) % p for x in diff], p)
        g, s, t = h.xgcd(c)                                      # s h + t c = 1
        assert g.degree() == 0
        h1 = (ee * t * nmod_poly([pow(int(g[0]), -1, p)], p)) % h
        hh = [int(h[i]) + p * int(h1[i]) for i in range(h.degree() + 1)]
        out.append((h, nmod_poly(hh, p**2)))
    return out

def power_stable(r, p):
    """True if no ratio of two distinct Q_p-conjugate unit roots can be a root of unity."""
    res = []
    fs = unit_factors_mod_p2(r, p)
    if fs is None: return None
    for h, hh in fs:
        d = h.degree()
        if d == 1: res.append((1, True)); continue
        x = nmod_poly([0, 1], p**2); acc = nmod_poly([1], p**2); e = p**d - 1
        base = x % hh
        while e:
            if e & 1: acc = (acc * base) % hh
            base = (base * base) % hh; e >>= 1
        co = [int(acc[i]) - (1 if i == 0 else 0) for i in range(d)]
        assert all(c % p == 0 for c in co)
        w = nmod_poly([(c // p) % p for c in co], p)             # = -eps mod p, in F_p[T]/(h)
        ok = True
        for l in {q for q in range(2, d + 1) if d % q == 0 and all(q % t for t in range(2, q))}:
            k = d // l
            wp = w
            for _ in range(k):
                wp = pow_mod(wp, p, h)
            ok &= (wp != w)
        res.append((d, ok))
    return res

def pow_mod(a, e, h):
    acc = nmod_poly([1], h.modulus()); base = a % h
    while e:
        if e & 1: acc = (acc * base) % h
        base = (base * base) % h; e >>= 1
    return acc

def powers():
    primes = sorted({int(f.split('_p')[1].split('_')[0]) for f in os.listdir(D) if f.endswith('_N3.txt')})
    print('Powers of Frobenius (unit-root polynomials mod p^2): factor degree, "no root-of-unity ratio" certified')
    for p in primes:
        for r, name in ((1, 'slope 1'), (2, 'slope 2')):
            ps = power_stable(r, p)
            print(f'  p = {p:3d} {name}:', 'not squarefree mod p' if ps is None else ' '.join(f'{d}:{"yes" if ok else "NO"}' for d, ok in sorted(ps)))

if __name__ == '__main__':
    powers()
