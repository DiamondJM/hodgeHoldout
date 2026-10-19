"""For fixed D, compute the subspace of A' in span{(3,1) monomials of V} admitting a certificate (mod p)."""
import time
from flint import nmod_mat
from koszul import mctx, MX, mFERMAT, mCOUP1, mCOUP2, mF_HOLD, mmono, P, pchar
from cert import char, char_add, unit, monoms_char, NV
MON31 = [(0,0,1,0,4,1),(0,0,3,0,0,3),(0,1,0,4,1,0),(0,2,1,2,0,1),(0,3,0,0,3,0),(3,0,0,3,0,0)]
def span31(F, D, label):
    t0 = time.time(); d = D.total_degree(); chD = pchar(D); chA = char(MON31[0])
    J = [F.derivative(i) for i in range(NV)]; dD = [D.derivative(i) for i in range(NV)]
    chN = [char_add(char_add(chA, chD), unit(i)) for i in range(NV)]
    chH = char_add(chA, char_add(chD, chD))
    unk = [('N', i, e) for i in range(NV) for e in monoms_char(d+1, chN[i])]
    nN = len(unk)
    unk += [('H', -1, e) for e in monoms_char(2*d-6, chH)]
    nH = len(unk) - nN
    unk += [('A', -1, m) for m in MON31]
    rows = {}
    def row(tag, m):
        k = (tag, m)
        if k not in rows: rows[k] = len(rows)
        return rows[k]
    cols = []
    for (kind, i, e) in unk:
        col = {}; m = mmono(e)
        if kind == 'N':
            for q, tag in ((m*J[i], 1), (D*m.derivative(i) - m*dD[i], 2)):
                for mm, c in zip(q.monoms(), q.coeffs()): col[row(tag, mm)] = (col.get(row(tag, mm), 0) + c) % P
        elif kind == 'H':
            q = -F*m
            for mm, c in zip(q.monoms(), q.coeffs()): col[row(2, mm)] = c
        else:
            q = -m*D
            for mm, c in zip(q.monoms(), q.coeffs()): col[row(1, mm)] = c
        cols.append(col)
    nr = len(rows); M = nmod_mat(nr, len(cols), P)
    for c, col in enumerate(cols):
        for r, v in col.items(): M[r, c] = v
    X, nul = M.nullspace()
    # projection of nullspace onto the 6 A-coordinates
    base = nN + nH
    proj = nmod_mat(nul, 6, P)
    for j in range(nul):
        for a in range(6): proj[j, a] = int(X[base + a, j])
    rk = proj.rank()
    print(f"[{label}] d={d}: nullity={nul}, dim of supported (3,1)-subspace = {rk}  ({time.time()-t0:.0f}s)", flush=True)
    if rk:
        R, r = proj.rref()
        for i in range(r):
            print("   A' direction:", {MON31[a]: int(R[i,a]) for a in range(6) if int(R[i,a])})
    return rk
if __name__ == "__main__":
    x0,x1,x2,y0,y1,y2 = MX
    D0 = x0**6+x1**6+x2**6; D1 = D0 + mCOUP1 + mCOUP2; Qy = y0**6+y1**6+y2**6
    span31(mFERMAT, D0, "Fermat D0")
    span31(mFERMAT, x0**6 + y1**6 + y2**6, "Fermat x0^6+y1^6+y2^6")
    for lab, D in [("D0", D0), ("D1", D1), ("Qy", Qy), ("D1^2", D1**2), ("D0^2", D0**2), ("Qy^2", Qy**2), ("D1^3", D1**3), ("Qy^3", Qy**3)]:
        span31(mF_HOLD, D, "Hold " + lab)
