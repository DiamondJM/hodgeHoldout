"""
Per-character bilinear search:  unknown D (degree d, character chi, Y-even), N, H.
E1 (linear in N,D), E2 (bilinear in D,N; linear in H).
"""
import itertools, sys, time, os, subprocess, random
from cert import *

def all_chars():
    seen = set()
    for e in itertools.product(range(6), repeat=6):
        seen.add(char(e))
    return sorted(seen)

CHARS = all_chars()
YEVEN_CHARS = [c for c in CHARS if (c[3] + c[4] + c[5]) % 2 == 0]


def block_data(F, d, chD, EA=EA):
    """Enumerate unknowns for D, N_i, H in the character block."""
    Dm = monoms_char(d, chD)
    chN = [char_add(char_add(EA, chD), unit(i)) for i in range(NV)]
    Nm = [monoms_char(d + 1, chN[i]) for i in range(NV)]
    chH = char_add(EA, char_add(chD, chD))
    Hm = monoms_char(2 * d - 6, chH)
    return Dm, Nm, Hm


def e1_admissible_dim(F, d, chD, A=A, p=PRIME):
    """dim of {D in block : A*D in J(F)}  (necessary for E1)."""
    Dm, Nm, Hm = block_data(F, d, chD)
    if not Dm:
        return 0, 0
    J = [F.derivative(i) for i in range(NV)]
    rows = {}
    cols = []  # list of dict row->val
    def getrow(m):
        if m not in rows:
            rows[m] = len(rows)
        return rows[m]
    for i in range(NV):
        for e in Nm[i]:
            p_ = mono(e) * J[i]
            cols.append({getrow(m): int(c) for m, c in zip(p_.monoms(), p_.coeffs())})
    nN = len(cols)
    for e in Dm:
        p_ = A * mono(e)
        cols.append({getrow(m): int(c) for m, c in zip(p_.monoms(), p_.coeffs())})
    nr = len(rows)
    M = nmod_mat(nr, len(cols), p)
    for c, col in enumerate(cols):
        for r, v in col.items():
            M[r, c] = v % p
    rk_all = M.rank()
    M2 = nmod_mat(nr, nN, p)
    for c in range(nN):
        for r, v in cols[c].items():
            M2[r, c] = v % p
    rk_N = M2.rank()
    # dimension of D-space mapping into col space of N-part:
    # = len(Dm) - (rk_all - rk_N)
    return len(Dm) - (rk_all - rk_N), len(Dm)


def scan_admissible(F, degrees, out=None):
    res = {}
    for d in degrees:
        tot = 0
        for ch in YEVEN_CHARS:
            adm, nD = e1_admissible_dim(F, d, ch)
            if adm > 0:
                res[(d, ch)] = (adm, nD)
                tot += 1
                line = f"d={d} ch={ch} admissible={adm}/{nD}"
                print(line, flush=True)
                if out: print(line, file=out, flush=True)
        print(f"== d={d}: {tot} admissible characters", flush=True)
        if out: print(f"== d={d}: {tot} admissible characters", file=out, flush=True)
    return res


if __name__ == "__main__":
    degs = [int(a) for a in sys.argv[1:]] or list(range(6, 13))
    with open(f"admissible_{degs[0]}_{degs[-1]}.log", "w") as out:
        scan_admissible(F_HOLD, degs, out)
