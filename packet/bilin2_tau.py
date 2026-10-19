"""
tau-symmetric bilinear search (tau: x2 <-> y2 is an automorphism of F fixing A).
Restrict to D with D o tau = eps*D, N with tau.N = eps*N, H with H o tau = H.
Usage: python3 bilin2_tau.py d nproc eps
"""
import sys, os, time, random, subprocess, re
from multiprocessing import Pool
from flint import nmod_mat
from cert import *
from bilin import block_data, YEVEN_CHARS
from bilin2 import (P, WORK, sparse_cols_to_nmod, nullspace_basis, left_nullspace_basis, quad_str, lin_str,
                    run_msolve_file, parse_gb, F_multiples_linear_forms, singular_components)

TAU = [0, 1, 5, 3, 4, 2]  # index permutation x2(2) <-> y2(5)

def tau_e(e):
    e = list(e); e[2], e[5] = e[5], e[2]; return tuple(e)

def tau_poly(p):
    return ctx.from_dict({tau_e(m): c for m, c in zip(p.monoms(), p.coeffs())})


def sym_basis(items, eps):
    """items: list of hashable unknown labels u; tau acting as a function tau_u. Returns list of (u, tau_u) orbit reps
    with sign eps (drop orbits where u == tau_u and eps == -1)."""
    seen = set(); out = []
    idx = {u: i for i, u in enumerate(items)}
    return idx


def build_reduced_tau(F, d, chD, eps, A=A, p=P):
    Dm, Nm, Hm = block_data(F, d, chD)
    if not Dm: return None
    # check tau-stability of the block
    if any(tau_e(e) not in set(Dm) for e in Dm): return None
    J = [F.derivative(i) for i in range(NV)]
    Nidx = [(i, e) for i in range(NV) for e in Nm[i]]
    nN, nD, nH = len(Nidx), len(Dm), len(Hm)
    Nset = {u: k for k, u in enumerate(Nidx)}
    Dset = {e: k for k, e in enumerate(Dm)}
    Hset = {e: k for k, e in enumerate(Hm)}
    def tau_N(u): return (TAU[u[0]], tau_e(u[1]))
    # orbit representatives
    def reps(items, tau_f, sgn):
        out = []; seen = set()
        for u in items:
            if u in seen: continue
            v = tau_f(u); seen.add(u); seen.add(v)
            if v == u:
                if sgn == 1: out.append((u, None))
            else:
                out.append((u, v))
        return out
    Nreps = reps(Nidx, tau_N, eps); Dreps = reps(Dm, tau_e, eps); Hreps = reps(Hm, tau_e, 1)
    # ---- E1 matrix on symmetrized unknowns (N reps then D reps)
    rows1 = {}
    def r1(m):
        if m not in rows1: rows1[m] = len(rows1)
        return rows1[m]
    cols1 = []
    def addcol(col, q, sign=1):
        for m, c in zip(q.monoms(), q.coeffs()):
            rr = r1(m); col[rr] = (col.get(rr, 0) + sign * int(c)) % p
    for (u, v) in Nreps:
        col = {}
        addcol(col, mono(u[1]) * J[u[0]])
        if v is not None: addcol(col, mono(v[1]) * J[v[0]], eps)
        cols1.append(col)
    for (e, v) in Dreps:
        col = {}
        addcol(col, -A * mono(e))
        if v is not None: addcol(col, -A * mono(v), eps)
        cols1.append(col)
    M1 = sparse_cols_to_nmod(cols1, len(rows1), p)
    T = nullspace_basis(M1)
    r = len(T)
    nNr, nDr = len(Nreps), len(Dreps)
    if r == 0: return dict(r=0, Dm=Dm)
    # expand T to full N, D coordinate vectors (nN x r), (nD x r)
    TN = nmod_mat(nN, r, p); TD = nmod_mat(nD, r, p)
    for j, vec in enumerate(T):
        for k, (u, v) in enumerate(Nreps):
            c = vec[k]
            if c:
                TN[Nset[u], j] = c
                if v is not None: TN[Nset[v], j] = (eps * c) % p
        for k, (e, v) in enumerate(Dreps):
            c = vec[nNr + k]
            if c:
                TD[Dset[e], j] = c
                if v is not None: TD[Dset[v], j] = (eps * c) % p
    if all(TD[i, j] == 0 for i in range(nD) for j in range(r)):
        return dict(r=r, Dm=Dm, TD=None)
    # ---- E2
    rows2 = {}
    def r2(m):
        if m not in rows2: rows2[m] = len(rows2)
        return rows2[m]
    Hcols = []
    for (e, v) in Hreps:
        col = {}
        q = -F * mono(e)
        for m, c in zip(q.monoms(), q.coeffs()): col[r2(m)] = (col.get(r2(m), 0) + int(c)) % p
        if v is not None:
            q = -F * mono(v)
            for m, c in zip(q.monoms(), q.coeffs()): col[r2(m)] = (col.get(r2(m), 0) + int(c)) % p
        Hcols.append(col)
    Q = {}
    dD = [(mono(ed), [mono(ed).derivative(i) for i in range(NV)]) for ed in Dm]
    for k, (i, e) in enumerate(Nidx):
        m_ = mono(e); dm = m_.derivative(i)
        for l in range(nD):
            Dl, dDl = dD[l]
            q = Dl * dm - m_ * dDl[i]
            if q.is_zero(): continue
            Q[(k, l)] = {r2(m): int(c) for m, c in zip(q.monoms(), q.coeffs())}
    nrows2 = len(rows2)
    MH = sparse_cols_to_nmod(Hcols, nrows2, p) if Hreps else nmod_mat(nrows2, 0, p)
    Y = left_nullspace_basis(MH) if Hreps else [[1 if i == j else 0 for i in range(nrows2)] for j in range(nrows2)]
    qn = len(Y)
    if qn == 0: return dict(r=r, Dm=Dm, TD=TD, TN=TN, quadrics=[], nquad=0, nN=nN, nD=nD, nH=nH)
    Ym = nmod_mat(qn, nrows2, p)
    for a, vec in enumerate(Y):
        for i, x in enumerate(vec):
            if x: Ym[a, i] = x
    keys = list(Q.keys())
    QM = nmod_mat(nrows2, len(keys), p)
    for c, key in enumerate(keys):
        for rr, v in Q[key].items(): QM[rr, c] = v % p
    YQ = Ym * QM
    TNt = TN.transpose()
    quadrics = []
    for a in range(qn):
        W = nmod_mat(nN, nD, p); nz = False
        for c, (k, l) in enumerate(keys):
            v = YQ[a, c]
            if v != 0: W[k, l] = v; nz = True
        if not nz: continue
        Qa = TNt * W * TD
        coeffs = {}
        for i in range(r):
            for j in range(r):
                v = int(Qa[i, j])
                if v:
                    key = (i, j) if i <= j else (j, i)
                    coeffs[key] = (coeffs.get(key, 0) + v) % p
        coeffs = {k: v for k, v in coeffs.items() if v}
        if coeffs: quadrics.append(coeffs)
    # dedupe identical quadrics
    uniq = {}
    for qd in quadrics: uniq[tuple(sorted(qd.items()))] = qd
    quadrics = list(uniq.values())
    return dict(r=r, Dm=Dm, TD=TD, TN=TN, quadrics=quadrics, nquad=qn, nN=nN, nD=nD, nH=nH, nNr=nNr, nDr=nDr)


def analyze_tau(F, d, chD, eps, log_path, threads=1):
    t0 = time.time()
    with open(log_path, "a") as log:
        R = build_reduced_tau(F, d, chD, eps)
        if R is None:
            print(f"d={d} ch={chD} eps={eps}: block not tau-stable or empty", file=log, flush=True); return []
        if R["r"] == 0 or R.get("TD") is None:
            print(f"d={d} ch={chD} eps={eps}: excluded (E1)", file=log, flush=True); return []
        r, TD, Dm, quads = R["r"], R["TD"], R["Dm"], R["quadrics"]
        nD = len(Dm)
        print(f"d={d} ch={chD} eps={eps}: nN={R['nN']}->{R['nNr']} nD={nD}->{R['nDr']} r={r} quadrics={len(quads)} build={time.time()-t0:.1f}s", file=log, flush=True)
        lin_triv_rows = F_multiples_linear_forms(F, d, chD, Dm)
        TDl = [[int(TD[i, j]) for j in range(r)] for i in range(nD)]
        triv_t = []
        for row in lin_triv_rows:
            v = [sum(int(row[i]) * TDl[i][j] for i in range(nD)) % P for j in range(r)]
            if any(v): triv_t.append(v)
        if not triv_t:
            print(f"  no nontrivial D directions", file=log, flush=True); return []
        rng = random.Random(777 + d * 31 + sum(chD) + eps)
        charts = []
        for _ in range(min(2, len(triv_t))):
            v = [0] * r
            for row in triv_t:
                a = rng.randrange(1, P)
                for j in range(r): v[j] = (v[j] + a * row[j]) % P
            charts.append(v)
        tvars = [f"t{i}" for i in range(r)]
        findings = []
        for jc, ch in enumerate(charts):
            lines = [quad_str(q) for q in quads] + [lin_str(ch, -1)]
            tag = f"tau{eps}_d{d}_{''.join(map(str, chD))}_c{jc}"
            fn, fo = f"{WORK}/{tag}.ms", f"{WORK}/{tag}.out"
            with open(fn, "w") as f:
                f.write(",".join(tvars) + "\n" + f"{P}\n" + ",\n".join(lines) + "\n")
            t1 = time.time()
            res = run_msolve_file(fn, fo, threads=threads, timeout=1800)
            if res is None:
                print(f"  chart {jc}: TIMEOUT", file=log, flush=True); findings.append((jc, "TIMEOUT")); continue
            gb = parse_gb(res)
            if gb is None:
                print(f"  chart {jc}: FAIL {res[:100]!r}", file=log, flush=True); findings.append((jc, "FAIL")); continue
            if gb == ["1"]:
                print(f"  chart {jc}: empty ({time.time()-t1:.1f}s)", file=log, flush=True); os.remove(fn); os.remove(fo); continue
            lin_triv = [lin_str(v, 0) for v in triv_t]
            comps, raw = singular_components(gb, tvars, lin_triv)
            nontriv = [c for c in comps if not c[1]]
            print(f"  chart {jc}: NONEMPTY gb={len(gb)} comps={[(c[0], c[1]) for c in comps]} ({time.time()-t1:.1f}s)", file=log, flush=True)
            if nontriv:
                print(f"  !!! NONTRIVIAL d={d} ch={chD} eps={eps} chart={jc}", file=log, flush=True)
                for c in nontriv: print(f"    dim={c[0]}\n{c[2]}", file=log, flush=True)
                findings.append((jc, nontriv))
        print(f"  done ch={chD} eps={eps} total {time.time()-t0:.1f}s", file=log, flush=True)
        return findings


FSEL = {"hold": F_HOLD, "fermat": FERMAT}

def worker(args):
    d, chD, eps, fsel, log_path = args
    try:
        return (chD, analyze_tau(FSEL[fsel], d, chD, eps, log_path))
    except Exception as ex:
        with open(log_path, "a") as log: print(f"d={d} ch={chD} eps={eps}: EXCEPTION {ex!r}", file=log, flush=True)
        return (chD, [("EXC", repr(ex))])


def tau_char(ch):
    return char(tau_e(ch))

if __name__ == "__main__":
    d = int(sys.argv[1]); nproc = int(sys.argv[2]); eps = int(sys.argv[3])
    fsel = sys.argv[4] if len(sys.argv) > 4 else "hold"
    chars = [c for c in YEVEN_CHARS if tau_char(c) == c]
    log_path = f"bilin2tau_{fsel}_d{d}_eps{eps}.log"
    with open(log_path, "a") as log: print(f"=== START d={d} eps={eps} tau-stable Y-even chars={len(chars)}", file=log, flush=True)
    allf = []
    with Pool(nproc) as pool:
        for chD, f in pool.imap_unordered(worker, [(d, ch, eps, fsel, log_path) for ch in chars]):
            if f: allf.append((chD, f))
    with open(log_path, "a") as log:
        print(f"=== DONE d={d} eps={eps}; blocks with findings: {len(allf)} {[(c, [x[0] for x in f]) for c, f in allf]}", file=log, flush=True)
