"""Exhaustive exclusion by linearisation: for a character class {m_1..m_k} of y-free monomials of degree d,
H = sum h_j m_j.  Unknowns w_{j,i,m} (standing for h_j * coefficient of monomial m in P_i) and s_{jl} (h_j h_l, one per distinct product m_j m_l):
   sum w_{j,i,m} C_{j,i,m} - sum_{j<=l} s_{jl} R_{jl} = 0  mod F^2,
with C_{j,i,m} = 4 g^2 (m_j T_i(m) - m g d_i m_j),  R_{jl} = (2 - delta_jl) m_j m_l a (48 y^5 - e).
If every kernel vector has s = 0, no H in the class admits a solution (mod p)."""
import sys, time, random
from collections import defaultdict
from ct import *

def class_test(d, cls, synthetic=False, seed=0):
    k = len(cls); Ms = [mono(m) for m in cls]
    R = {}
    for j in range(k):
        for l in range(j, k):
            key = tuple(a_ + b_ for a_, b_ in zip(cls[j], cls[l]))     # distinct products m_j m_l only
            if key not in R: R[key] = divmod(Ms[j]*Ms[l]*SRC, F2)[1]
    target = poly_char(next(iter(R.values())))
    cols = []
    for j in range(k):
        dH = [Ms[j].derivative(t) for t in range(1, 6)]
        for i in range(5):
            off = None
            for m in monos(d + 2):
                if off is None:
                    c0 = column(Ms[j], dH, i, m)
                    if c0 == 0: continue
                    off = cadd(poly_char(c0), char(m), -1)
                if cadd(char(m), off) != target: continue
                cols.append(divmod(column(Ms[j], dH, i, m), F2)[1])
    rhs = [R[key] for key in sorted(R)]
    if synthetic:      # replace the source by one that is solvable by construction for H = m_1
        rng = random.Random(seed); n1 = len(cols)//k
        rhs = [sum((rng.randrange(1, P)*cols[t] for t in range(n1)), ctx.from_dict({}))]
    rows = {}
    for p in cols + rhs:
        for mm in p.monoms(): rows.setdefault(tuple(mm), len(rows))
    nw, ns = len(cols), len(rhs)
    M = nmod_mat(len(rows), nw + ns, P)
    for jj, p in enumerate(cols + rhs):
        for mm, cf in zip(p.monoms(), p.coeffs()): M[rows[tuple(mm)], jj] = int(cf)
    Mw = nmod_mat(len(rows), max(nw, 1), P)
    for jj, p in enumerate(cols):
        for mm, cf in zip(p.monoms(), p.coeffs()): Mw[rows[tuple(mm)], jj] = int(cf)
    rw = Mw.rank() if nw else 0
    # dimension of the projection of the kernel onto the s-coordinates = ns - (rank M - rank Mw)
    return ns - (M.rank() - rw), nw, ns, len(rows)

if __name__ == '__main__':
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    # controls
    cl = defaultdict(list)
    for m in monos(4, yfree=True): cl[char(m)].append(m)
    c4 = next(v for v in cl.values() if len(v) == 2)
    print('control (synthetic solvable source):', class_test(4, c4[:1], synthetic=True)[0], '(expect 1)')
    print('control (same H, real source)      :', class_test(4, c4[:1])[0], '(expect 0 or 1)')
    for d in range(1, dmax + 1):
        cl = defaultdict(list)
        for m in monos(d, yfree=True): cl[char(m)].append(m)
        t0 = time.time(); alive = []
        for ch, cls in sorted(cl.items()):
            s_dim, nw, ns, nr = class_test(d, cls)
            if s_dim > 0: alive.append((cls, s_dim, ns))
        print(f'degree {d}: {len(cl)} classes ({sum(len(v) for v in cl.values())} monomials), '
              f'{len(alive)} not excluded by the linear relaxation  ({time.time()-t0:.0f}s)', flush=True)
        for cls, s_dim, ns in alive: print('    class', [str(mono(m)) for m in cls], 's-kernel dim', s_dim, 'of', ns)
