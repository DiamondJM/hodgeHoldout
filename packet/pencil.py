"""
Pencil search:  D(b) = D1 + b*D2  (same degree, same character, Y-even), find b in F_p (or F_p-bar)
for which a certificate exists.  Uses E1 particular solutions (linear in b), Koszul kernel,
E2 reduced mod F:  M(b) t = -r(b)  with M(b) = M0 + b M1, r(b) = r0 + b r1 + b^2 r2.
Special b's are roots of det(L [M(b) R | r(b)]) for random projections L, R.
"""
import sys, time, random, itertools
from flint import nmod_mat, nmod_poly, nmod
from koszul import mctx, MX, mFERMAT, mCOUP1, mCOUP2, mF_HOLD, mA, mmono, P, pchar, solve_dense
from cert import char, char_add, unit, monoms_char, NV

random.seed(2024)


def e1_data(F, A, d, chD):
    chA = pchar(A)
    J = [F.derivative(i) for i in range(NV)]
    chN = [char_add(char_add(chA, chD), unit(i)) for i in range(NV)]
    Nidx = [(i, e) for i in range(NV) for e in monoms_char(d + 1, chN[i])]
    rows = {}
    def row(m):
        if m not in rows: rows[m] = len(rows)
        return rows[m]
    cols = []
    for (i, e) in Nidx:
        q = mmono(e) * J[i]
        cols.append({row(m): c for m, c in zip(q.monoms(), q.coeffs())})
    nr, nc = len(rows), len(cols)
    M = nmod_mat(nr, nc, P)
    for c, col in enumerate(cols):
        for r, v in col.items(): M[r, c] = v
    # left nullspace
    X, nul = M.transpose().nullspace()
    Y = [[int(X[i, j]) for i in range(nr)] for j in range(nul)]
    # pseudo-inverse via rref of [M | I]
    big = nmod_mat(nr, nc + nr, P)
    for c, col in enumerate(cols):
        for r, v in col.items(): big[r, c] = v
    for r in range(nr): big[r, nc + r] = 1
    R, rk = big.rref()
    piv = []
    for r in range(rk):
        for j in range(nc):
            if R[r, j] != 0:
                piv.append(j); break
        else:
            piv.append(None)
    return dict(J=J, Nidx=Nidx, rows=rows, nr=nr, nc=nc, Y=Y, R=R, rk=rk, piv=piv, chA=chA)


def e1_solve(dat, D, A):
    """returns (w = Y.(A D) obstruction vector, particular N (list of polys) ignoring obstruction)"""
    AD = A * D
    b = [0] * dat['nr']
    for m, c in zip(AD.monoms(), AD.coeffs()):
        if m in dat['rows']: b[dat['rows'][m]] = c
        else:
            # monomial outside row set: cannot be hit at all
            return None, None
    w = []
    for y in dat['Y']:
        s = 0
        for i, yi in enumerate(y):
            if yi and b[i]: s = (s + yi * b[i]) % P
        w.append(s)
    R, nc, nr = dat['R'], dat['nc'], dat['nr']
    N = [mctx.from_dict({}) for _ in range(NV)]
    for r in range(dat['rk']):
        pj = dat['piv'][r]
        if pj is None: continue
        s = 0
        for i in range(nr):
            if b[i]:
                v = int(R[r, nc + i])
                if v: s = (s + v * b[i]) % P
        if s:
            i, e = dat['Nidx'][pj]
            N[i] += mmono(e, s)
    return w, N


def koszul_gens(F, dat, d, chD):
    J = dat['J']; chA = dat['chA']
    gens = []
    for i in range(NV):
        for j in range(i + 1, NV):
            chm = char_add(char_add(chA, chD), char_add(unit(i), unit(j)))
            for e in monoms_char(d - 4, chm):
                gens.append((i, j, mmono(e)))
    return gens


def B_of(D, dD, Nv):
    return D * sum(Nv[i].derivative(i) for i in range(NV)) - sum(Nv[i] * dD[i] for i in range(NV))


def B_koszul(D, dD, J, gens, F):
    cols = []
    for (i, j, m) in gens:
        Km = J[j] * m.derivative(i) - J[i] * m.derivative(j)
        KD = J[j] * dD[i] - J[i] * dD[j]
        cols.append((D * Km - m * KD) % F)
    return cols


def poly_vec(polys, rows):
    out = []
    for q in polys:
        out.append({rows.setdefault(m, len(rows)): c for m, c in zip(q.monoms(), q.coeffs())})
    return out


def pencil(F, D1, D2, label="", A=mA, verbose=True):
    t0 = time.time()
    d = D1.total_degree(); assert D2.total_degree() == d
    chD = pchar(D1); assert pchar(D2) == chD
    dat = e1_data(F, A, d, chD)
    w1, N1 = e1_solve(dat, D1, A)
    w2, N2 = e1_solve(dat, D2, A)
    if w1 is None or w2 is None:
        return "E1-impossible", []
    # E1 condition: w1 + b w2 = 0
    nz1, nz2 = any(w1), any(w2)
    b_forced = None
    if not nz1 and not nz2:
        pass  # all b
    elif not nz2:
        return "E1-none", []
    else:
        # need w1 = -b w2 : check proportional
        k = next(i for i, v in enumerate(w2) if v)
        b_forced = (-w1[k] * pow(w2[k], P - 2, P)) % P
        if any((w1[i] + b_forced * w2[i]) % P for i in range(len(w1))):
            return "E1-none", []
    gens = koszul_gens(F, dat, d, chD)
    J = dat['J']
    dD1 = [D1.derivative(i) for i in range(NV)]; dD2 = [D2.derivative(i) for i in range(NV)]
    rows = {}
    K1 = poly_vec(B_koszul(D1, dD1, J, gens, F), rows)
    K2 = poly_vec(B_koszul(D2, dD2, J, gens, F), rows)
    r0 = poly_vec([B_of(D1, dD1, N1) % F], rows)[0]
    r1 = poly_vec([(B_of(D1, dD1, N2) + B_of(D2, dD2, N1)) % F], rows)[0]
    r2 = poly_vec([B_of(D2, dD2, N2) % F], rows)[0]
    nr, nc = len(rows), len(gens)

    def mats_at(b):
        M = nmod_mat(nr, nc + 1, P)
        for c in range(nc):
            for r, v in K1[c].items(): M[r, c] = v
            for r, v in K2[c].items(): M[r, c] = (int(M[r, c]) + b * v) % P
        for r, v in r0.items(): M[r, nc] = v
        for r, v in r1.items(): M[r, nc] = (int(M[r, nc]) + b * v) % P
        for r, v in r2.items(): M[r, nc] = (int(M[r, nc]) + b * b % P * v) % P
        return M

    def solvable_at(b):
        M = mats_at(b)
        Rm, rank = M.rref()
        if rank == 0: return True
        r = rank - 1
        return not (Rm[r, nc] != 0 and all(Rm[r, c] == 0 for c in range(nc)))

    if b_forced is not None:
        ok = solvable_at(b_forced)
        if verbose: print(f"[{label}] d={d} forced b={b_forced}: solvable={ok} ({time.time()-t0:.0f}s)", flush=True)
        return ("FOUND" if ok else "none"), ([b_forced] if ok else [])
    # generic rank
    bg = random.randrange(1, P)
    Mg = mats_at(bg)
    Msub = nmod_mat(nr, nc, P)
    for r in range(nr):
        for c in range(nc): Msub[r, c] = int(Mg[r, c])
    rho = Msub.rank()
    if solvable_at(bg):
        if verbose: print(f"[{label}] d={d}: solvable at generic b (rho={rho})!", flush=True)
        return "GENERIC", [bg]
    # projected determinant polynomial in b, degree <= rho+2
    found = None
    for trial in range(2):
        L = nmod_mat(rho + 1, nr, P); Rr = nmod_mat(nc, rho, P)
        for i in range(rho + 1):
            for j in range(nr): L[i, j] = random.randrange(P)
        for i in range(nc):
            for j in range(rho): Rr[i, j] = random.randrange(P)
        npts = rho + 4
        xs, ys = [], []
        for _ in range(npts):
            b = random.randrange(P)
            M = mats_at(b)
            MR = nmod_mat(nr, rho + 1, P)
            Msub = nmod_mat(nr, nc, P)
            for r in range(nr):
                for c in range(nc): Msub[r, c] = int(M[r, c])
            prod = Msub * Rr
            for r in range(nr):
                for c in range(rho): MR[r, c] = int(prod[r, c])
                MR[r, rho] = int(M[r, nc])
            det = (L * MR).det()
            xs.append(b); ys.append(int(det))
        # interpolate
        poly = lagrange_interp(xs, ys)
        if poly is None or poly.degree() < 0 or all(int(c) == 0 for c in poly.coeffs()):
            if verbose: print(f"[{label}] d={d}: projected det identically zero?! (rho={rho})", flush=True)
            return "ZERO-DET", []
        roots = [int(r) for r, mult in poly.roots()] if hasattr(poly, 'roots') else []
        fac = poly.factor()
        irr = [(f.degree(), m) for f, m in fac[1]]
        cand = set(roots)
        if found is None: found = cand
        else: found &= cand
        if verbose: print(f"[{label}] d={d} rho={rho} trial{trial}: det-degree={poly.degree()} F_p-roots={len(roots)} factor-degrees={irr}", flush=True)
    good = [b for b in sorted(found) if solvable_at(b)]
    if verbose: print(f"[{label}] d={d}: verified special b's = {good} ({time.time()-t0:.0f}s)", flush=True)
    return ("FOUND" if good else "none"), good


def lagrange_interp(xs, ys):
    n = len(xs)
    # Newton form mod P via flint nmod_poly
    res = nmod_poly([0], P)
    basis = nmod_poly([1], P)
    coeffs = []
    # divided differences
    dd = [y % P for y in ys]
    table = list(dd)
    newton = []
    for k in range(n):
        newton.append(table[0])
        if k == n - 1: break
        new = []
        for i in range(len(table) - 1):
            den = (xs[i + k + 1] - xs[i]) % P
            new.append(((table[i + 1] - table[i]) * pow(den, P - 2, P)) % P)
        table = new
    for k in range(n):
        res = res + basis * newton[k]
        basis = basis * nmod_poly([(-xs[k]) % P, 1], P)
    return res


if __name__ == "__main__":
    x0, x1, x2, y0, y1, y2 = MX
    D0 = x0**6 + x1**6 + x2**6
    print(pencil(mFERMAT, x0**6 + x1**6, x2**6, "Fermat x0^6+x1^6 | x2^6"))
    print(pencil(mF_HOLD, D0, y1**6, "Hold D0 | y1^6"))
