"""
Certificate solver for (D, N) with
  E1: sum_i N_i dF/dx_i = A * D
  E2: D * div(N) - N(D) = F * H      (i.e. B_D(N) in (F))
Variables (x0,x1,x2,y0,y1,y2).  F is G-invariant for the finite abelian group
G = {zeta in mu_6^6 : zeta^c1 = zeta^c2 = 1},  c1=(3,1,0,1,1,0), c2=(0,3,1,0,1,1).
If D is G-semi-invariant, the unknowns N_i, H live in single character blocks.
"""
import itertools, sys, time
from functools import lru_cache
import flint
from flint import fmpq_mpoly_ctx, fmpq, fmpz, nmod_mat, fmpq_mat, fmpz_mat

ctx = fmpq_mpoly_ctx.get(('x0', 'x1', 'x2', 'y0', 'y1', 'y2'))
X = ctx.gens()
x0, x1, x2, y0, y1, y2 = X
NV = 6
C1 = (3, 1, 0, 1, 1, 0)
C2 = (0, 3, 1, 0, 1, 1)

FERMAT = sum(v**6 for v in X)
COUP1 = x0**3 * x1 * y0 * y1
COUP2 = x1**3 * x2 * y1 * y2
F_HOLD = FERMAT + COUP1 + COUP2
A = x0**3 * y0**3
EA = (3, 0, 0, 3, 0, 0)

PRIME = 2**31 - 1


def char(e):
    """Canonical representative of the G-character of monomial x^e."""
    e = [v % 6 for v in e]
    k = e[3]
    e = [(e[i] - k * C1[i]) % 6 for i in range(6)]
    k = e[2]
    e = [(e[i] - k * C2[i]) % 6 for i in range(6)]
    return tuple(e)


def char_add(a, b):
    return char([a[i] + b[i] for i in range(6)])


def char_sub(a, b):
    return char([a[i] - b[i] for i in range(6)])


def poly_char(p):
    """Return the character if p is semi-invariant, else None."""
    cs = {char(m) for m in p.monoms()}
    return cs.pop() if len(cs) == 1 else None


def ydeg_parity(e):
    return (e[3] + e[4] + e[5]) % 2


@lru_cache(maxsize=None)
def monoms_of_degree(n):
    out = []
    for c in itertools.combinations(range(n + NV - 1), NV - 1):
        e = []
        prev = -1
        for ci in c:
            e.append(ci - prev - 1)
            prev = ci
        e.append(n + NV - 1 - prev - 1)
        out.append(tuple(e))
    return out


@lru_cache(maxsize=None)
def monoms_char(n, ch):
    if n < 0:
        return []
    return [e for e in monoms_of_degree(n) if char(e) == ch]


def mono(e, c=1):
    return ctx.from_dict({tuple(e): fmpq(c)})


def unit(i):
    e = [0] * 6
    e[i] = 1
    return tuple(e)


def build_system(F, D, A=A, EA=EA, verbose=True):
    """Return (cols, rows, entries(dict (r,c)->int), rhs dict r->int, unknown labels)."""
    d = D.total_degree()
    chD = poly_char(D)
    assert chD is not None, "D must be G-semi-invariant"
    J = [F.derivative(i) for i in range(NV)]
    dD = [D.derivative(i) for i in range(NV)]
    chN = [char_add(char_add(EA, chD), unit(i)) for i in range(NV)]  # char of N_i monomials
    chH = char_add(EA, char_add(chD, chD))
    unknowns = []  # (kind, i, exps)
    for i in range(NV):
        for e in monoms_char(d + 1, chN[i]):
            unknowns.append(('N', i, e))
    nN = len(unknowns)
    for e in monoms_char(2 * d - 6, chH):
        unknowns.append(('H', -1, e))
    nH = len(unknowns) - nN
    rows = {}  # (eq, monomial) -> row index
    entries = {}

    def row(tag, m):
        key = (tag, m)
        if key not in rows:
            rows[key] = len(rows)
        return rows[key]

    def addpoly(col, tag, p):
        for m, c in zip(p.monoms(), p.coeffs()):
            r = row(tag, m)
            entries[(r, col)] = entries.get((r, col), 0) + int(c)

    for col, (kind, i, e) in enumerate(unknowns):
        m = mono(e)
        if kind == 'N':
            addpoly(col, 1, m * J[i])
            addpoly(col, 2, D * m.derivative(i) - m * dD[i])
        else:
            addpoly(col, 2, -F * m)
    rhs = {}
    for m, c in zip((A * D).monoms(), (A * D).coeffs()):
        rhs[row(1, m)] = int(c)
    if verbose:
        print(f"  d={d} chD={chD} unknowns N={nN} H={nH} rows={len(rows)} nnz={len(entries)}", flush=True)
    return unknowns, rows, entries, rhs


def solvable_mod_p(unknowns, rows, entries, rhs, p=PRIME):
    nr, nc = len(rows), len(unknowns)
    if nc == 0:
        return (all(v % p == 0 for v in rhs.values())), 0, 0
    M = nmod_mat(nr, nc + 1, p)
    for (r, c), v in entries.items():
        M[r, c] = v % p
    for r, v in rhs.items():
        M[r, nc] = v % p
    R, rank = M.rref()
    # inconsistent iff last column is a pivot column: last pivot row has pivot at nc
    incons = False
    if rank > 0:
        r = rank - 1
        if R[r, nc] != 0 and all(R[r, c] == 0 for c in range(nc)):
            incons = True
    rank_m = rank - 1 if incons else rank
    return (not incons), rank_m, nc - rank_m


def solve_Q(unknowns, rows, entries, rhs):
    """Particular solution over Q via rref of augmented matrix. Returns dict col->fmpq or None."""
    nr, nc = len(rows), len(unknowns)
    M = fmpq_mat(nr, nc + 1)
    for (r, c), v in entries.items():
        M[r, c] = fmpq(v)
    for r, v in rhs.items():
        M[r, nc] = fmpq(v)
    R, rank = M.rref()
    sol = {}
    for r in range(rank):
        # find pivot
        piv = None
        for c in range(nc + 1):
            if R[r, c] != 0:
                piv = c
                break
        if piv is None:
            continue
        if piv == nc:
            return None  # inconsistent
        sol[piv] = R[r, nc]
    return sol


def assemble(unknowns, sol):
    N = [ctx.from_dict({}) for _ in range(NV)]
    H = ctx.from_dict({})
    for col, (kind, i, e) in enumerate(unknowns):
        c = sol.get(col, fmpq(0))
        if c == 0:
            continue
        if kind == 'N':
            N[i] += mono(e, c)
        else:
            H += mono(e, c)
    return N, H


def verify(F, D, N, H, A=A):
    e1 = sum(N[i] * F.derivative(i) for i in range(NV)) - A * D
    B = D * sum(N[i].derivative(i) for i in range(NV)) - sum(N[i] * D.derivative(i) for i in range(NV))
    e2 = B - F * H
    g = D.gcd(F)
    ok = e1.is_zero() and e2.is_zero() and g.is_constant() and not D.is_zero()
    nontriv = not all(n.is_zero() for n in N)
    return ok and nontriv, e1.is_zero(), e2.is_zero(), g.is_constant()


def try_D(F, D, label="", verbose=True, solve=True):
    t0 = time.time()
    if verbose:
        print(f"[{label}] deg D = {D.total_degree()}, Y-even={all(ydeg_parity(m)==0 for m in D.monoms())}", flush=True)
    unk, rows, ent, rhs = build_system(F, D, verbose=verbose)
    ok, rk, nul = solvable_mod_p(unk, rows, ent, rhs)
    if verbose:
        print(f"  mod-p: solvable={ok} rank={rk} nullity={nul}  ({time.time()-t0:.1f}s)", flush=True)
    if not ok or not solve:
        return ok, None
    sol = solve_Q(unk, rows, ent, rhs)
    if sol is None:
        print("  inconsistent over Q (mod-p false positive)")
        return False, None
    N, H = assemble(unk, sol)
    v = verify(F, D, N, H)
    if verbose:
        print(f"  verify: {v}  ({time.time()-t0:.1f}s)", flush=True)
    return v[0], (N, H)


if __name__ == "__main__":
    pass
