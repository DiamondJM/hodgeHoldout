import itertools, random
from gm import *
from cert import char
FERMAT = {}
for i in range(6):
    e = [0]*6; e[i] = 6; FERMAT[tuple(e)] = 1
C1 = {(3,1,0,1,1,0): 1}; C2 = {(0,3,1,0,1,1): 1}
both = {**C1, **C2}
chA1 = char((4,1,1,4,1,1))
basis = [a for a in itertools.product(range(5), repeat=6) if sum(a) in (6,12,18) and char([x+1 for x in a]) == chA1]
basis.sort(key=lambda a: sum(a))
random.seed(7); t0 = random.randrange(2, P)
for fam_label, Fb, Cd in [("diag", FERMAT, both), ("C2line", {**FERMAT, **C1}, C2), ("C1line", {**FERMAT, **C2}, C1)]:
    print("=====", fam_label)
    for a in basis:
        q = sum(a)//6
        rA, vecs = run(Fb, Cd, a, t0, f"{fam_label} {a} type({4-q},{q})", maxj=22)
