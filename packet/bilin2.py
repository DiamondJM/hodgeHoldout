"""
Reduced bilinear search per (d, character):
  1. parametrize E1 solutions (N, D) = T t  (nullspace mod p)
  2. project E2 modulo F*H  -> quadrics in t
  3. per chart on D, run msolve (GB mod p); nontrivial -> decompose in Singular,
     discard components with D in (F).
Usage: python3 bilin2.py d [nprocs] [charlist-file]
"""
import sys, os, time, subprocess, itertools, re
from multiprocessing import Pool
from flint import nmod_mat, nmod
from cert import *
from bilin import block_data, YEVEN_CHARS

P = 268435399
WORK = os.path.dirname(os.path.abspath(__file__)) + "/msolve_work2"
os.makedirs(WORK, exist_ok=True)


def sparse_cols_to_nmod(cols, nrows, p=P):
    M = nmod_mat(nrows, len(cols), p)
    for c, col in enumerate(cols):
        for r, v in col.items():
            M[r, c] = v % p
    return M


def nullspace_basis(M):
    """Return list of column vectors (as python lists mod p) spanning the right nullspace."""
    X, nullity = M.nullspace()
    nr = X.nrows()
    basis = []
    for j in range(nullity):
        basis.append([int(X[i, j]) for i in range(nr)])
    return basis


def left_nullspace_basis(M):
    return nullspace_basis(M.transpose())


def build_reduced(F, d, chD, A=A, p=P):
    Dm, Nm, Hm = block_data(F, d, chD)
    if not Dm:
        return None
    J = [F.derivative(i) for i in range(NV)]
    Nidx = [(i, e) for i in range(NV) for e in Nm[i]]
    nN, nD, nH = len(Nidx), len(Dm), len(Hm)
    # ---- E1 matrix: columns N then D
    rows1 = {}
    def r1(m):
        if m not in rows1: rows1[m] = len(rows1)
        return rows1[m]
    cols1 = []
    for (i, e) in Nidx:
        q = mono(e) * J[i]
        cols1.append({r1(m): int(c) for m, c in zip(q.monoms(), q.coeffs())})
    for e in Dm:
        q = -A * mono(e)
        cols1.append({r1(m): int(c) for m, c in zip(q.monoms(), q.coeffs())})
    M1 = sparse_cols_to_nmod(cols1, len(rows1), p)
    T = nullspace_basis(M1)  # list of vectors length nN+nD
    r = len(T)
    if r == 0:
        return dict(r=0, Dm=Dm, Nm=Nm, Hm=Hm)
    # T as matrix (nN+nD) x r
    Tm = nmod_mat(nN + nD, r, p)
    for j, v in enumerate(T):
        for i, x in enumerate(v):
            if x: Tm[i, j] = x
    TN = nmod_mat(nN, r, p); TD = nmod_mat(nD, r, p)
    for j in range(r):
        for i in range(nN):
            if Tm[i, j] != 0: TN[i, j] = Tm[i, j]
        for i in range(nD):
            if Tm[nN + i, j] != 0: TD[i, j] = Tm[nN + i, j]
    # quick exit: if TD == 0 then D forced 0
    if all(TD[i, j] == 0 for i in range(nD) for j in range(r)):
        return dict(r=r, Dm=Dm, Nm=Nm, Hm=Hm, TD=None)
    # ---- E2: rows = monomials of degree 2d in char; H columns; bilinear tensor
    rows2 = {}
    def r2(m):
        if m not in rows2: rows2[m] = len(rows2)
        return rows2[m]
    Hcols = []
    for e in Hm:
        q = -F * mono(e)
        Hcols.append({r2(m): int(c) for m, c in zip(q.monoms(), q.coeffs())})
    Q = {}  # (k, l) -> {row: coeff}
    dD = []
    for l, ed in enumerate(Dm):
        Dl = mono(ed)
        dD.append((Dl, [Dl.derivative(i) for i in range(NV)]))
    for k, (i, e) in enumerate(Nidx):
        m_ = mono(e); dm = m_.derivative(i)
        for l in range(nD):
            Dl, dDl = dD[l]
            q = Dl * dm - m_ * dDl[i]
            if q.is_zero(): continue
            Q[(k, l)] = {r2(m): int(c) for m, c in zip(q.monoms(), q.coeffs())}
    nrows2 = len(rows2)
    MH = sparse_cols_to_nmod(Hcols, nrows2, p) if nH > 0 else nmod_mat(nrows2, 0, p)
    if nH > 0:
        Y = left_nullspace_basis(MH)  # list of row-vectors length nrows2
    else:
        Y = [[1 if i == j else 0 for i in range(nrows2)] for j in range(nrows2)]
    qn = len(Y)
    if qn == 0:
        return dict(r=r, Dm=Dm, Nm=Nm, Hm=Hm, TD=TD, TN=TN, quadrics=[], nquad=0)
    Ym = nmod_mat(qn, nrows2, p)
    for a, v in enumerate(Y):
        for i, x in enumerate(v):
            if x: Ym[a, i] = x
    # W[a] = nN x nD matrix with entries Y[a] . Q[k,l]
    # compute via: for each (k,l): vector Q_kl (nrows2) -> Ym * Q_kl (qn)
    # Batch: stack Q_kl as columns of a matrix (nrows2 x nkl), multiply.
    keys = list(Q.keys())
    nkl = len(keys)
    QM = nmod_mat(nrows2, nkl, p)
    for c, key in enumerate(keys):
        for rr, v in Q[key].items():
            QM[rr, c] = v % p
    YQ = Ym * QM  # qn x nkl
    # Now quadric a: sum_{(k,l)} YQ[a, c] * n_k(t) d_l(t), with n = TN t, d = TD t
    # => t^T (TN^T W_a TD) t.  Build W_a sparse then multiply.
    TNt = TN.transpose()
    quadrics = []
    for a in range(qn):
        W = nmod_mat(nN, nD, p)
        nz = False
        for c, (k, l) in enumerate(keys):
            v = YQ[a, c]
            if v != 0:
                W[k, l] = v; nz = True
        if not nz:
            continue
        Qa = TNt * W * TD  # r x r
        coeffs = {}
        for i in range(r):
            for j in range(r):
                v = int(Qa[i, j])
                if v:
                    key = (i, j) if i <= j else (j, i)
                    coeffs[key] = (coeffs.get(key, 0) + v) % p
        coeffs = {k: v for k, v in coeffs.items() if v}
        if coeffs:
            quadrics.append(coeffs)
    return dict(r=r, Dm=Dm, Nm=Nm, Hm=Hm, TD=TD, TN=TN, quadrics=quadrics, nquad=qn,
                nN=nN, nD=nD, nH=nH, nrows1=len(rows1), nrows2=nrows2)


def quad_str(coeffs, p=P):
    terms = []
    for (i, j), v in coeffs.items():
        if i == j:
            terms.append(f"{v}*t{i}^2")
        else:
            terms.append(f"{v}*t{i}*t{j}")
    return "+".join(terms)


def lin_str(vec, const, p=P):
    terms = [f"{int(v)}*t{i}" for i, v in enumerate(vec) if int(v)]
    if const % p:
        terms.append(str(const % p))
    return "+".join(terms) if terms else "0"


def run_msolve_file(fn, fo, elim=0, threads=1, timeout=3600):
    cmd = ["msolve", "-f", fn, "-o", fo, "-g", "2", "-t", str(threads)]
    if elim: cmd += ["-e", str(elim)]
    try:
        subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    try:
        return open(fo).read()
    except FileNotFoundError:
        return ""


def parse_gb(text):
    s = "".join(l for l in text.splitlines(True) if not l.startswith('#')).strip().rstrip(':').strip()
    if not (s.startswith('[') and s.endswith(']')):
        return None
    body = s[1:-1].strip()
    return [q.strip() for q in body.split(',\n')] if body else []


def F_multiples_linear_forms(F, d, chD, Dm, p=P):
    """Linear forms (as rows over D-coords) vanishing on F*R_{d-6} inside the block."""
    if d < 6:
        return [[1 if i == j else 0 for i in range(len(Dm))] for j in range(len(Dm))]
    chE = char_sub(chD, (0,) * 6)  # F invariant, so E has char chD
    Em = monoms_char(d - 6, chE)
    idx = {m: i for i, m in enumerate(Dm)}
    cols = []
    for e in Em:
        q = F * mono(e)
        col = {}
        for m, c in zip(q.monoms(), q.coeffs()):
            col[idx[m]] = int(c)
        cols.append(col)
    if not cols:
        return [[1 if i == j else 0 for i in range(len(Dm))] for j in range(len(Dm))]
    M = sparse_cols_to_nmod(cols, len(Dm), p)
    return left_nullspace_basis(M)


def singular_components(polys, vars_, lin_trivial, p=P):
    """Decompose ideal; return list of (dim, is_trivial, generators)."""
    src = ['LIB "primdec.lib";', f'ring r = {p}, ({",".join(vars_)}), dp;',
           f'ideal I = {",".join(polys) if polys else "0"};', 'I = std(I);',
           f'ideal S = {",".join(lin_trivial) if lin_trivial else "0"};',
           'list L = minAssGTZ(I); int i;',
           'for(i=1;i<=size(L);i++){ ideal Ci = std(L[i]); print("COMP dim "+string(dim(Ci))+" trivial "+string(size(reduce(S,Ci))==0)); print(L[i]); print("ENDCOMP"); }',
           'quit;']
    r = subprocess.run(["Singular", "-q"], input="\n".join(src), capture_output=True, text=True, timeout=1800)
    out = r.stdout
    comps = []
    for blk in re.findall(r"COMP dim (\d+) trivial (\d)\n(.*?)ENDCOMP", out, flags=re.S):
        comps.append((int(blk[0]), blk[1] == "1", blk[2].strip()))
    return comps, out


def analyze(F, d, chD, log_path, threads=1):
    t0 = time.time()
    with open(log_path, "a") as log:
        R = build_reduced(F, d, chD)
        if R is None or R["r"] == 0 or R.get("TD") is None:
            print(f"d={d} ch={chD}: excluded (E1)  r={0 if R is None else R['r']}", file=log, flush=True)
            return []
        r, TD, Dm = R["r"], R["TD"], R["Dm"]
        nD = len(Dm)
        quads = R["quadrics"]
        print(f"d={d} ch={chD}: nN={R['nN']} nD={nD} nH={R['nH']} r={r} quadrics={len(quads)}/{R['nquad']} build={time.time()-t0:.1f}s", file=log, flush=True)
        lin_triv_rows = F_multiples_linear_forms(F, d, chD, Dm)
        # express trivial-linear-forms in t: row . (TD t)
        TDl = [[int(TD[i, j]) for j in range(r)] for i in range(nD)]
        def row_dot_TD(row):
            return [sum(int(row[i]) * TDl[i][j] for i in range(nD)) % P for j in range(r)]
        triv_t = [row_dot_TD(row) for row in lin_triv_rows]
        triv_t = [v for v in triv_t if any(v)]
        findings = []
        tvars = [f"t{i}" for i in range(r)]
        # charts: l_j(D) = 1, l_i(D) = 0 (i<j) for annihilator forms l of F*R_{d-6};
        # this excludes trivial solutions D in (F) and covers every D not in (F).
        import random
        rng = random.Random(12345 + d * 7919 + sum(chD))
        NCH = int(os.environ.get("NCHARTS", "2"))
        charts = []
        for _ in range(min(NCH, len(triv_t))):
            v = [0] * r
            for row in triv_t:
                a = rng.randrange(1, P)
                for j in range(r):
                    v[j] = (v[j] + a * row[j]) % P
            charts.append(v)
        print(f"  random annihilator charts: {len(charts)} (from {len(triv_t)} forms)", file=log, flush=True)
        for jc in range(len(charts)):
            lines = [quad_str(q) for q in quads]
            lines.append(lin_str(charts[jc], -1))
            tag = f"d{d}_{''.join(map(str, chD))}_c{jc}"
            fn, fo = f"{WORK}/{tag}.ms", f"{WORK}/{tag}.out"
            with open(fn, "w") as f:
                f.write(",".join(tvars) + "\n" + f"{P}\n" + ",\n".join(lines) + "\n")
            t1 = time.time()
            res = run_msolve_file(fn, fo, threads=threads, timeout=900)
            if res is None:
                print(f"  chart {jc}: TIMEOUT", file=log, flush=True); findings.append((jc, "TIMEOUT")); continue
            gb = parse_gb(res)
            if gb is None:
                print(f"  chart {jc}: PARSE FAIL {res[:200]}", file=log, flush=True); findings.append((jc, "PARSEFAIL")); continue
            if gb == ["1"]:
                print(f"  chart {jc}: empty ({time.time()-t1:.1f}s)", file=log, flush=True)
                continue
            # nontrivial: decompose
            lin_triv = [lin_str(v, 0) for v in triv_t]
            comps, raw = singular_components(gb, tvars, lin_triv)
            nontriv = [c for c in comps if not c[1]]
            print(f"  chart {jc}: NONEMPTY gb={len(gb)} comps={[(c[0], c[1]) for c in comps]} ({time.time()-t1:.1f}s)", file=log, flush=True)
            if nontriv:
                print(f"  !!! NONTRIVIAL COMPONENTS d={d} ch={chD} chart={jc}", file=log, flush=True)
                for c in nontriv:
                    print(f"    dim={c[0]}\n{c[2]}", file=log, flush=True)
                findings.append((jc, nontriv))
            if not comps:
                print(f"    (singular output) {raw[:1500]}", file=log, flush=True)
                findings.append((jc, "SINGULAR-FAIL"))
        print(f"  done ch={chD} total {time.time()-t0:.1f}s", file=log, flush=True)
        return findings


FSEL = {"hold": F_HOLD, "c1": FERMAT + COUP1, "c2": FERMAT + COUP2, "fermat": FERMAT}[os.environ.get("FSEL", "hold")]

def worker(args):
    d, chD, log_path = args
    try:
        return (chD, analyze(FSEL, d, chD, log_path))
    except Exception as ex:
        with open(log_path, "a") as log:
            print(f"d={d} ch={chD}: EXCEPTION {ex!r}", file=log, flush=True)
        return (chD, [("EXC", repr(ex))])


if __name__ == "__main__":
    d = int(sys.argv[1])
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    chars = YEVEN_CHARS
    if len(sys.argv) > 3:
        chars = [tuple(int(c) for c in s.strip()) for s in open(sys.argv[3]) if s.strip()]
    log_path = f"bilin2_{os.environ.get('FSEL', 'hold')}_d{d}.log" if os.environ.get("FSEL", "hold") != "hold" else f"bilin2_d{d}.log"
    with open(log_path, "a") as log:
        print(f"=== START d={d} chars={len(chars)} nproc={nproc}", file=log, flush=True)
    tasks = [(d, ch, log_path) for ch in chars]
    allf = []
    with Pool(nproc) as pool:
        for chD, f in pool.imap_unordered(worker, tasks):
            if f:
                allf.append((chD, f))
    with open(log_path, "a") as log:
        print(f"=== DONE d={d}; blocks with findings: {len(allf)}", file=log, flush=True)
        for chD, f in allf:
            print(f"   {chD}: {[x[0] for x in f]}", file=log, flush=True)
