"""
A-divisible ansatz:  N = A * g,  D = g(F)  (so E1 holds automatically),
E2:  g(F) * div(A g) - A * g(g(F))  in (F).
Per (degree d, Y-even character chi_g):  g_i has degree d-5 and character chi_g + e_i.
Quadratic system in the coefficients of g; chart: l(g(F)) = 1 for a random l vanishing on F*R_{d-6}.
Usage: python3 ansatz.py d [nproc] [FSEL]
"""
import sys, os, time, random, subprocess, re
from multiprocessing import Pool
from flint import nmod_mat
from koszul import mctx, MX, mFERMAT, mCOUP1, mCOUP2, mF_HOLD, mA, mmono, P
from cert import char, char_add, char_sub, unit, monoms_char, NV
from bilin import YEVEN_CHARS

WORK = os.path.dirname(os.path.abspath(__file__)) + "/msolve_ansatz"
os.makedirs(WORK, exist_ok=True)
FSEL = {"hold": mF_HOLD, "c1": mFERMAT + mCOUP1, "c2": mFERMAT + mCOUP2, "fermat": mFERMAT}


def build(F, d, chg, A=mA):
    J = [F.derivative(i) for i in range(NV)]
    unk = []  # (i, exps)
    for i in range(NV):
        for e in monoms_char(d - 5, char_add(chg, unit(i))):
            unk.append((i, e))
    u = len(unk)
    if u == 0:
        return None
    Dk = [mmono(e) * J[i] for (i, e) in unk]            # Delta_k
    delk = [(A * mmono(e)).derivative(i) for (i, e) in unk]  # div part
    dDk = [[Dl.derivative(i) for i in range(NV)] for Dl in Dk]
    # quadratic coefficients: B = sum_{k,l} g_k g_l (Dk[k]*delk[l] - A*m_k*dDk[l][i_k])
    eqs = {}  # monomial -> {(k,l): coeff}
    for k, (ik, ek) in enumerate(unk):
        Amk = A * mmono(ek)
        for l in range(u):
            B = (Dk[k] * delk[l] - Amk * dDk[l][ik]) % F
            if B.is_zero():
                continue
            key = (k, l) if k <= l else (l, k)
            for m, c in zip(B.monoms(), B.coeffs()):
                row = eqs.setdefault(m, {})
                row[key] = (row.get(key, 0) + c) % P
    return unk, Dk, eqs


def F_annihilator_forms(F, d, chg, Dk):
    """random linear form on D-space vanishing on F*R_{d-6}, expressed on g-coordinates."""
    # D-space monomials: degree d, char chg
    Dm = monoms_char(d, chg)
    idx = {m: i for i, m in enumerate(Dm)}
    nD = len(Dm)
    # F*R_{d-6}
    cols = []
    if d >= 6:
        for e in monoms_char(d - 6, chg):
            q = F * mmono(e)
            cols.append({idx[m]: c for m, c in zip(q.monoms(), q.coeffs())})
    if cols:
        M = nmod_mat(nD, len(cols), P)
        for c, col in enumerate(cols):
            for r, v in col.items():
                M[r, c] = v
        X, nul = M.transpose().nullspace()
        ann = [[int(X[i, j]) for i in range(nD)] for j in range(nul)]
    else:
        ann = [[1 if i == j else 0 for i in range(nD)] for j in range(nD)]
    if not ann:
        return None
    rng = random.Random(hash((d, chg)) & 0xffff)
    l = [0] * nD
    for row in ann:
        a = rng.randrange(1, P)
        for i in range(nD):
            l[i] = (l[i] + a * row[i]) % P
    # l(D(g)) = sum_k g_k * l(Dk[k])
    lin = []
    for Dkk in Dk:
        s = 0
        for m, c in zip(Dkk.monoms(), Dkk.coeffs()):
            s = (s + l[idx[m]] * c) % P
        lin.append(s)
    return lin


def run_block(args):
    d, chg, fsel, log_path = args
    F = FSEL[fsel]
    t0 = time.time()
    try:
        res = build(F, d, chg)
        if res is None:
            return (chg, "nounk")
        unk, Dk, eqs = res
        u = len(unk)
        lin = F_annihilator_forms(F, d, chg, Dk)
        if lin is None or not any(lin):
            with open(log_path, "a") as log:
                print(f"d={d} ch={chg}: u={u} eqs={len(eqs)}  D(g) always in (F) -> skip", file=log, flush=True)
            return (chg, "trivial")
        names = [f"g{k}" for k in range(u)]
        lines = []
        for m, row in eqs.items():
            terms = []
            for (k, l), c in row.items():
                if c:
                    terms.append(f"{c}*g{k}*g{l}" if k != l else f"{c}*g{k}^2")
            if terms:
                lines.append("+".join(terms))
        chart = "+".join(f"{c}*g{k}" for k, c in enumerate(lin) if c) + f"+{P-1}"
        lines.append(chart)
        tag = f"{fsel}_d{d}_{''.join(map(str, chg))}"
        fn, fo = f"{WORK}/{tag}.ms", f"{WORK}/{tag}.out"
        with open(fn, "w") as f:
            f.write(",".join(names) + "\n" + f"{P}\n" + ",\n".join(lines) + "\n")
        t1 = time.time()
        try:
            subprocess.run(["msolve", "-f", fn, "-o", fo, "-g", "2", "-t", "1"], capture_output=True, text=True, timeout=1800)
        except subprocess.TimeoutExpired:
            with open(log_path, "a") as log:
                print(f"d={d} ch={chg}: u={u} eqs={len(lines)} TIMEOUT", file=log, flush=True)
            return (chg, "timeout")
        txt = open(fo).read() if os.path.exists(fo) else ""
        body = "".join(l for l in txt.splitlines(True) if not l.startswith('#')).strip().rstrip(':').strip()
        if body == "":
            status = "FAIL(empty)"
        elif body.strip("[]").strip() == "1":
            status = "empty"
        else:
            status = "NONEMPTY"
        with open(log_path, "a") as log:
            print(f"d={d} ch={chg}: u={u} eqs={len(lines)} build={t1-t0:.1f}s msolve={time.time()-t1:.1f}s -> {status}", file=log, flush=True)
            if status == "NONEMPTY":
                print(f"!!! NONEMPTY d={d} ch={chg} file={fo}\n{body[:3000]}", file=log, flush=True)
        if status == "empty":
            os.remove(fn); os.remove(fo)
        return (chg, status)
    except Exception as ex:
        with open(log_path, "a") as log:
            print(f"d={d} ch={chg}: EXCEPTION {ex!r}", file=log, flush=True)
        return (chg, "exc")


if __name__ == "__main__":
    d = int(sys.argv[1])
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    fsel = sys.argv[3] if len(sys.argv) > 3 else "hold"
    log_path = f"ansatz_{fsel}_d{d}.log"
    with open(log_path, "a") as log:
        print(f"=== START d={d} fsel={fsel}", file=log, flush=True)
    tasks = [(d, ch, fsel, log_path) for ch in YEVEN_CHARS]
    stats = {}
    with Pool(nproc) as pool:
        for ch, st in pool.imap_unordered(run_block, tasks):
            stats[st] = stats.get(st, 0) + 1
    with open(log_path, "a") as log:
        print(f"=== DONE d={d}: {stats}", file=log, flush=True)
