"""
Fixed-D certificate test mod p with Koszul parametrization of the E1 kernel
and E2 reduced modulo F by division.  Scales to larger degrees than cert.try_D.
"""
import sys, time, itertools
from flint import nmod_mpoly_ctx, nmod_mat
from cert import char, char_add, char_sub, unit, monoms_char, poly_char, ydeg_parity, NV, EA

P = 268435399
mctx = nmod_mpoly_ctx.get(('x0', 'x1', 'x2', 'y0', 'y1', 'y2'), modulus=P)
MX = mctx.gens()
mx0, mx1, mx2, my0, my1, my2 = MX
mFERMAT = sum(v**6 for v in MX)
mCOUP1 = mx0**3 * mx1 * my0 * my1
mCOUP2 = mx1**3 * mx2 * my1 * my2
mF_HOLD = mFERMAT + mCOUP1 + mCOUP2
mA = mx0**3 * my0**3


def mmono(e, c=1):
    return mctx.from_dict({tuple(e): c % P})


def to_mod(p):
    """fmpq_mpoly with integer coefficients -> nmod_mpoly"""
    d = {}
    for m, c in zip(p.monoms(), p.coeffs()):
        c = int(c)  # must be integral
        d[tuple(m)] = c % P
    return mctx.from_dict(d)


def pchar(p):
    cs = {char(m) for m in p.monoms()}
    assert len(cs) == 1, "not semi-invariant"
    return cs.pop()


def solve_dense(cols, nrows, rhs, verbose=False):
    """cols: list of dict row->val; rhs: dict row->val. Returns (solvable, particular solution list or None, rank)."""
    nc = len(cols)
    M = nmod_mat(nrows, nc + 1, P)
    for c, col in enumerate(cols):
        for r, v in col.items():
            M[r, c] = v % P
    for r, v in rhs.items():
        M[r, nc] = v % P
    R, rank = M.rref()
    if rank > 0:
        r = rank - 1
        if R[r, nc] != 0 and all(R[r, c] == 0 for c in range(nc)):
            return False, None, rank - 1
    sol = [0] * nc
    for r in range(rank):
        piv = next(c for c in range(nc + 1) if R[r, c] != 0)
        sol[piv] = int(R[r, nc])
    return True, sol, rank


def test_D(F, D, label="", A=mA, verbose=True):
    t0 = time.time()
    d = D.total_degree()
    chD = pchar(D)
    chA = pchar(A)
    J = [F.derivative(i) for i in range(NV)]
    chN = [char_add(char_add(chA, chD), unit(i)) for i in range(NV)]
    # ---- E1 particular solution (dense, block)
    Nidx = [(i, e) for i in range(NV) for e in monoms_char(d + 1, chN[i])]
    rows = {}
    def row(m):
        if m not in rows: rows[m] = len(rows)
        return rows[m]
    cols = []
    for (i, e) in Nidx:
        q = mmono(e) * J[i]
        cols.append({row(m): c for m, c in zip(q.monoms(), q.coeffs())})
    AD = A * D
    rhs = {row(m): c for m, c in zip(AD.monoms(), AD.coeffs())}
    ok, sol, rank = solve_dense(cols, len(rows), rhs)
    if verbose:
        print(f"[{label}] d={d}: E1 unknowns={len(Nidx)} rows={len(rows)} rank={rank} solvable={ok} ({time.time()-t0:.0f}s)", flush=True)
    if not ok:
        return False
    Npart = [mctx.from_dict({}) for _ in range(NV)]
    for k, (i, e) in enumerate(Nidx):
        if sol[k]:
            Npart[i] += mmono(e, sol[k])
    # ---- E2: B_D(N) mod F, N = Npart + sum t * m * K_ij
    dD = [D.derivative(i) for i in range(NV)]
    def B_of(Nv):
        return D * sum(Nv[i].derivative(i) for i in range(NV)) - sum(Nv[i] * dD[i] for i in range(NV))
    Bpart = B_of(Npart) % F
    rows2 = {}
    def row2(m):
        if m not in rows2: rows2[m] = len(rows2)
        return rows2[m]
    rhs2 = {row2(m): (-c) % P for m, c in zip(Bpart.monoms(), Bpart.coeffs())}
    cols2 = []
    gens = []
    for i in range(NV):
        for j in range(i + 1, NV):
            chm = char_add(char_add(chA, chD), char_add(unit(i), unit(j)))
            for e in monoms_char(d - 4, chm):
                m = mmono(e)
                # K_ij = J_j e_i - J_i e_j ;  B_D(m K_ij) = D*K_ij(m) - m*K_ij(D)
                Km = J[j] * m.derivative(i) - J[i] * m.derivative(j)
                KD = J[j] * dD[i] - J[i] * dD[j]
                b = (D * Km - m * KD) % F
                if b.is_zero():
                    continue
                cols2.append({row2(mm): c for mm, c in zip(b.monoms(), b.coeffs())})
                gens.append((i, j, e))
    if verbose:
        print(f"[{label}] d={d}: E2 unknowns={len(cols2)} rows={len(rows2)} (build {time.time()-t0:.0f}s)", flush=True)
    if len(rows2) == 0:
        print(f"[{label}] SOLVABLE (B already 0)"); return True
    ok2, sol2, rank2 = solve_dense(cols2, len(rows2), rhs2)
    if verbose:
        print(f"[{label}] d={d}: E2 rank={rank2} solvable={ok2}  total {time.time()-t0:.0f}s", flush=True)
    return ok2


if __name__ == "__main__":
    D0 = mx0**6 + mx1**6 + mx2**6
    D1 = D0 + mCOUP1 + mCOUP2
    print("Fermat D0:", test_D(mFERMAT, D0, "FermatD0"))
    print("Fermat D0^2:", test_D(mFERMAT, D0**2, "FermatD0^2"))
    print("Hold D1:", test_D(mF_HOLD, D1, "HoldD1"))
    print("Hold D1^2:", test_D(mF_HOLD, D1**2, "HoldD1^2"))
    print("Hold D1^3:", test_D(mF_HOLD, D1**3, "HoldD1^3"))
