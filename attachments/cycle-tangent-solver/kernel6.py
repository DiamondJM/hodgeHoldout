import sys
from collections import defaultdict
from ct import *
def s_kernel(d, cls):
    k = len(cls); Ms = [mono(m) for m in cls]
    keys = [(j, l) for j in range(k) for l in range(j, k)]
    R = [divmod((1 if j == l else 2)*Ms[j]*Ms[l]*SRC, F2)[1] for j, l in keys]
    target = poly_char(R[0]); cols = []
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
    rows = {}
    for p in cols + R:
        for mm in p.monoms(): rows.setdefault(tuple(mm), len(rows))
    nw, ns = len(cols), len(R)
    M = nmod_mat(len(rows), nw + ns, P)
    for jj, p in enumerate(cols + R):
        for mm, cf in zip(p.monoms(), p.coeffs()): M[rows[tuple(mm)], jj] = int(cf) if jj < nw else (-int(cf)) % P
    X, nullity = M.nullspace()
    out = []
    for c in range(nullity):
        s = [int(X[nw + t, c]) for t in range(ns)]
        if any(s): out.append(s)
    return keys, out
if __name__ == '__main__':
    cl = defaultdict(list)
    for m in monos(6, yfree=True): cl[char(m)].append(m)
    cls = next(v for v in cl.values() if len(v) == 7)
    print('class:', [str(mono(m)) for m in cls])
    keys, ker = s_kernel(6, cls)
    # the s-projection is 1-dimensional: reduce the kernel vectors with nonzero s to one direction
    S = nmod_mat(7, 7, P)
    s = ker[0]
    for (j, l), v in zip(keys, s): S[j, l] = v; S[l, j] = v
    print('number of kernel vectors with s != 0:', len(ker), ' rank of S as symmetric 7x7:', S.rank())
    piv = next(t for t in range(len(s)) if s[t]); sc = pow(s[piv], P - 2, P)
    print('S (normalised):')
    for j in range(7): print('  ', [int(S[j, l])*sc % P for l in range(7)])
