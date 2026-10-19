"""Koszul-augmented ansatz: N = A*g + K, D = g(F).  Complete search for D in J(F)."""
import sys, os, time, random, subprocess
from multiprocessing import Pool
from flint import nmod_mat
from koszul import mctx, MX, mFERMAT, mCOUP1, mCOUP2, mF_HOLD, mA, mmono, P
from cert import char, char_add, unit, monoms_char, NV
from bilin import YEVEN_CHARS
from ansatz import build, F_annihilator_forms, FSEL
WORK = os.path.dirname(os.path.abspath(__file__)) + "/msolve_ansatz2"
os.makedirs(WORK, exist_ok=True)

def build2(F, d, chg, A=mA):
    res = build(F, d, chg, A)
    if res is None: return None
    unk, Dk, eqs = res
    J = [F.derivative(i) for i in range(NV)]
    chA = char((3,0,0,3,0,0))
    kos = []  # (i, j, m)
    for i in range(NV):
        for j in range(i+1, NV):
            for e in monoms_char(d - 4, char_add(char_add(chA, chg), char_add(unit(i), unit(j)))):
                kos.append((i, j, e))
    # bilinear terms: g_k * k_kappa * (Dk[k]*K_ij(m) - m*K_ij(Dk[k]))
    beqs = {}
    for kap, (i, j, e) in enumerate(kos):
        m = mmono(e)
        Km = J[j]*m.derivative(i) - J[i]*m.derivative(j)
        for k, Dkk in enumerate(Dk):
            KD = J[j]*Dkk.derivative(i) - J[i]*Dkk.derivative(j)
            B = (Dkk*Km - m*KD) % F
            for mm, c in zip(B.monoms(), B.coeffs()):
                row = beqs.setdefault(mm, {})
                row[(k, kap)] = (row.get((k, kap), 0) + c) % P
    return unk, Dk, eqs, kos, beqs

def run_block(args):
    d, chg, fsel, log_path = args
    F = FSEL[fsel]; t0 = time.time()
    try:
        res = build2(F, d, chg)
        if res is None: return (chg, "nounk")
        unk, Dk, eqs, kos, beqs = res
        u, v = len(unk), len(kos)
        lin = F_annihilator_forms(F, d, chg, Dk)
        if lin is None or not any(lin):
            return (chg, "trivial")
        names = [f"g{k}" for k in range(u)] + [f"k{k}" for k in range(v)]
        allm = set(eqs) | set(beqs)
        lines = []
        for mm in allm:
            terms = []
            for (k, l), c in eqs.get(mm, {}).items():
                if c: terms.append(f"{c}*g{k}*g{l}" if k != l else f"{c}*g{k}^2")
            for (k, kap), c in beqs.get(mm, {}).items():
                if c: terms.append(f"{c}*g{k}*k{kap}")
            if terms: lines.append("+".join(terms))
        lines.append("+".join(f"{c}*g{k}" for k, c in enumerate(lin) if c) + f"+{P-1}")
        tag = f"{fsel}_d{d}_{''.join(map(str, chg))}"
        fn, fo = f"{WORK}/{tag}.ms", f"{WORK}/{tag}.out"
        with open(fn, "w") as f:
            f.write(",".join(names) + "\n" + f"{P}\n" + ",\n".join(lines) + "\n")
        t1 = time.time()
        try:
            subprocess.run(["msolve", "-f", fn, "-o", fo, "-g", "2", "-t", "1"], capture_output=True, text=True, timeout=3600)
        except subprocess.TimeoutExpired:
            with open(log_path, "a") as log: print(f"d={d} ch={chg}: u={u} v={v} eqs={len(lines)} TIMEOUT", file=log, flush=True)
            return (chg, "timeout")
        txt = open(fo).read() if os.path.exists(fo) else ""
        body = "".join(l for l in txt.splitlines(True) if not l.startswith('#')).strip().rstrip(':').strip()
        status = "FAIL(empty)" if body == "" else ("empty" if body.strip("[]").strip() == "1" else "NONEMPTY")
        with open(log_path, "a") as log:
            print(f"d={d} ch={chg}: u={u} v={v} eqs={len(lines)} build={t1-t0:.1f}s msolve={time.time()-t1:.1f}s -> {status}", file=log, flush=True)
            if status == "NONEMPTY": print(f"!!! NONEMPTY d={d} ch={chg} file={fo}\n{body[:3000]}", file=log, flush=True)
        if status == "empty": os.remove(fn); os.remove(fo)
        return (chg, status)
    except Exception as ex:
        with open(log_path, "a") as log: print(f"d={d} ch={chg}: EXCEPTION {ex!r}", file=log, flush=True)
        return (chg, "exc")

if __name__ == "__main__":
    d = int(sys.argv[1]); nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    fsel = sys.argv[3] if len(sys.argv) > 3 else "hold"
    log_path = f"ansatz2_{fsel}_d{d}.log"
    with open(log_path, "a") as log: print(f"=== START d={d} fsel={fsel}", file=log, flush=True)
    stats = {}
    with Pool(nproc) as pool:
        for ch, st in pool.imap_unordered(run_block, [(d, ch, fsel, log_path) for ch in YEVEN_CHARS]):
            stats[st] = stats.get(st, 0) + 1
    with open(log_path, "a") as log: print(f"=== DONE d={d}: {stats}", file=log, flush=True)
