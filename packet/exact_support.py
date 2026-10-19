"""Exact rational support exclusions for the holdout: for each semi-invariant Y-even D, the complete
fixed-D linear system (full character-block numerator space, nonzero quotient allowed) for the whole
six-dimensional target-character sector.  rank(M) vs rank([M | A_1 D ... A_6 D]) over Q (fmpq_mat).
By the q=1 prescribed-support theorem (docs/01), failure excludes support on V(D) with any multiplicity."""
import time, itertools, sys
from flint import fmpq_mat, fmpq
from cert import *
MON31 = [(0,0,1,0,4,1),(0,0,3,0,0,3),(0,1,0,4,1,0),(0,2,1,2,0,1),(0,3,0,0,3,0),(3,0,0,3,0,0)]

def sector_test(F, D, label):
    t0 = time.time(); d = int(D.total_degree()); chD = poly_char(D); assert chD is not None
    chA = char(MON31[0]); J = [F.derivative(i) for i in range(NV)]; dD = [D.derivative(i) for i in range(NV)]
    chN = [char_add(char_add(chA, chD), unit(i)) for i in range(NV)]; chH = char_add(chA, char_add(chD, chD))
    unk = [('N', i, e) for i in range(NV) for e in monoms_char(d+1, chN[i])]
    unk += [('H', -1, e) for e in monoms_char(2*d-6, chH)]
    rows = {}
    def row(tag, m):
        k = (tag, m)
        if k not in rows: rows[k] = len(rows)
        return rows[k]
    cols = []
    for (kind, i, e) in unk:
        col = {}; m = mono(e)
        if kind == 'N':
            for q, tag in ((m*J[i], 1), (D*m.derivative(i) - m*dD[i], 2)):
                for mm, c in zip(q.monoms(), q.coeffs()): col[row(tag, mm)] = col.get(row(tag, mm), 0) + int(c)
        else:
            q = -F*m
            for mm, c in zip(q.monoms(), q.coeffs()): col[row(2, mm)] = int(c)
        cols.append(col)
    tcols = []
    for a in MON31:
        q = mono(a)*D; tcols.append({row(1, mm): int(c) for mm, c in zip(q.monoms(), q.coeffs())})
    nr, nc = len(rows), len(cols)
    M = fmpq_mat(nr, nc + 6)
    for c, col in enumerate(cols):
        for r, v in col.items(): M[r, c] = v
    for a, col in enumerate(tcols):
        for r, v in col.items(): M[r, nc + a] = v
    M0 = fmpq_mat(nr, nc)
    for c, col in enumerate(cols):
        for r, v in col.items(): M0[r, c] = v
    r0 = M0.rank(); r1 = M.rank()
    supported = 6 - (r1 - r0)
    print(f"{label:40} d={d:2} unknowns={nc:5} rows={nr:5} rank={r0:5} augmented={r1:5}  supported sector dim = {supported}  ({time.time()-t0:.0f}s)", flush=True)
    return supported

if __name__ == "__main__":
    Vs = list(X)
    def bs(B): return sum(Vs[i]**6 for i in B)
    D0 = bs([0,1,2]); D1 = D0 + COUP1 + COUP2; Qy = bs([3,4,5])
    Phi0 = x0**6 + y0**6 + COUP1; R = bs([1,2,4,5]) + COUP2
    Dsing = 432*Phi0**2 - (x1*y1)**6
    print("== Fermat controls (expect 4 and 3) =="); sector_test(FERMAT, D0, "Fermat join x0,x1,x2"); sector_test(FERMAT, bs([0,4,5]), "Fermat join x0,y1,y2")
    print("== holdout, degree 6 ==")
    cands = [("D0 = x0^6+x1^6+x2^6", D0), ("D1 = D0+C1+C2", D1), ("Qy", Qy), ("Phi0 = x0^6+y0^6+C1", Phi0), ("R = x1^6+x2^6+y1^6+y2^6+C2", R),
             ("x0^6+y0^6", x0**6+y0**6), ("x1^6-y1^6", x1**6-y1**6), ("x1^6+y1^6", x1**6+y1**6), ("x2^6-y2^6", x2**6-y2**6),
             ("U0^2+U1^2 = F-Psi", (x0**3+x1*y0*y1/2)**2 + (x1**3+x2*y1*y2/2)**2), ("C1+C2", COUP1+COUP2)]
    for S in itertools.combinations([1,2,4,5], 2):
        B1 = [0]+list(S); base = bs(B1)
        for cs, lab in [((0,0),""),((1,0),"+C1"),((0,1),"+C2"),((1,1),"+C1+C2")]:
            cands.append((f"block {B1}{lab}", base + cs[0]*COUP1 + cs[1]*COUP2))
    for lab, D in cands: sector_test(F_HOLD, D, lab)
    print("== holdout, degree 12 ==")
    for lab, D in [("Dsing = 432 Phi0^2 - (x1y1)^6", Dsing), ("D0*Qy", D0*Qy), ("x2^12 - x1^6 y1^6", x2**12 - x1**6*y1**6), ("(x2y2)^6-(x1y1)^6", (x2*y2)**6 - (x1*y1)**6), ("(x0x1)^6-(y0y1)^6", (x0*x1)**6-(y0*y1)**6)]:
        sector_test(F_HOLD, D, lab)
