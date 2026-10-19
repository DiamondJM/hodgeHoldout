import sys, itertools, time
from multiprocessing import Pool
from pencil import *
from cert import char, char_sub, ydeg_parity, monoms_of_degree
x0, x1, x2, y0, y1, y2 = MX

def order(ch):
    # order of character ch in (Z/6)^6/<c1,c2>
    for k in (1, 2, 3, 6):
        if char([k*v for v in ch]) == (0,)*6: return k
    return 6

def mono_pairs(maxdeg):
    out = []
    for e in range(1, maxdeg+1):
        ms = monoms_of_degree(e)
        for m1, m2 in itertools.combinations(ms, 2):
            k = order(char_sub(char(m1), char(m2)))
            if k == 1: continue
            if (k*ydeg_parity(m1)) % 2 or (k*ydeg_parity(m2)) % 2: continue  # Y-even
            if e*k > 18: continue
            out.append((m1, m2, k))
    return out

def job(args):
    m1, m2, k, lab = args
    D1 = mmono(m1)**k; D2 = mmono(m2)**k
    try:
        st, bs = pencil(mF_HOLD, D1, D2, lab, verbose=False)
    except Exception as ex:
        st, bs = f"EXC {ex!r}", []
    return (lab, k*sum(m1), st, bs)

if __name__ == "__main__":
    maxdeg = int(sys.argv[1]); nproc = int(sys.argv[2])
    pairs = mono_pairs(maxdeg)
    pairs.sort(key=lambda t: t[2]*sum(t[0]))
    tasks = [(m1, m2, k, f"{m1}^{k} + b {m2}^{k}") for (m1, m2, k) in pairs]
    log = open(f"pencil_mono_{maxdeg}.log", "a")
    print(f"=== {len(tasks)} pencils", file=log, flush=True)
    with Pool(nproc) as pool:
        for lab, deg, st, bs in pool.imap_unordered(job, tasks):
            print(f"deg={deg} {lab}: {st} {bs}", file=log, flush=True)
            if st in ("FOUND", "GENERIC"): print(f"!!! FOUND {lab} b={bs}", file=log, flush=True)
    print("=== DONE", file=log, flush=True)
