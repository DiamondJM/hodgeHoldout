import sys, itertools, time
from multiprocessing import Pool
from pencil import *
from pencil_run import order, job
from cert import char, char_sub, ydeg_parity, monoms_of_degree
def pairs_k2(degs):
    out = []
    for e in degs:
        ms = monoms_of_degree(e)
        for m1, m2 in itertools.combinations(ms, 2):
            k = order(char_sub(char(m1), char(m2)))
            if k != 2: continue
            if (2*ydeg_parity(m1)) % 2 or (2*ydeg_parity(m2)) % 2: continue
            out.append((m1, m2, 2))
    return out
if __name__ == "__main__":
    nproc = int(sys.argv[1])
    pairs = pairs_k2([4, 5, 6])
    pairs.sort(key=lambda t: sum(t[0]))
    tasks = [(m1, m2, k, f"{m1}^2 + b {m2}^2") for (m1, m2, k) in pairs]
    log = open("pencil_mono_k2.log", "a")
    print(f"=== {len(tasks)} pencils", file=log, flush=True)
    with Pool(nproc) as pool:
        for lab, deg, st, bs in pool.imap_unordered(job, tasks):
            print(f"deg={deg} {lab}: {st} {bs}", file=log, flush=True)
            if st in ("FOUND", "GENERIC"): print(f"!!! FOUND {lab} b={bs}", file=log, flush=True)
    print("=== DONE", file=log, flush=True)
