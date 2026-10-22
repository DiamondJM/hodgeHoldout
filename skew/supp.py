import sys, time
sys.path.insert(0, '/home/user/hodgeHoldout/sweep')
from fixed_d import *
X0,X1,X2,Y0,Y1,Y2 = V
Fr, q, Ar = parse_rec('/home/user/sextics/data/one-reflection/instance.rec')
Fs, _, As = parse_rec('/home/user/sextics/data/one-reflection-skew/instance.rec')
s = Y0**3 - Y1**3; S = Y0**3 + Y1**3; T = Y2**3; p = Y0*Y1
Ap = X0**3*S/2; Am = X0**3*s/2
cands = [('s^2+T^2', s**2+T**2), ('S^2+T^2', S**2+T**2), ('T^2-s^2/3', T**2 - s**2/3), ('T^2-S^2/3', T**2-S**2/3),
         ('(s^2+T^2)(S^2+T^2)? skip', None)]
which = sys.argv[1]
F = Fr if which == 'r' else Fs
for lab, D in cands:
    if D is None: continue
    for an, A in (('A', Ar), ('A+', Ap), ('A-', Am)):
        t = time.time(); ok = test(F, 1, A, D)
        print(which, lab, an, ok, f'{time.time()-t:.0f}s', flush=True)
