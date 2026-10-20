"""For every open instance, test whether F admits the holdout-type cover: one variable y of a block
and the other two (u,v) of that block written u = alpha*T, v = beta*T with T^6 = u^6+v^6 (so
alpha^6+beta^6=1), such that the pulled-back F is invariant under y <-> T.  Both blocks (Y and X)
are tried, with every choice of y.  Also report the target's companion exponent and quotient
source when the cover exists."""
import json, sys, itertools
import sympy as sp
sys.path.insert(0, '.')
root = '/home/user/hodge-computer/sextics/'
idx = json.load(open(root + 'data/index.json'))
Z = sp.symbols('X0 X1 X2 Y0 Y1 Y2')
al, be, T, y = sp.symbols('alpha beta T y')
loc = dict(zip(['X0','X1','X2','Y0','Y1','Y2'], Z))
def symmetric_after_cover(F, block, a):
    """block: indices of the three variables; a: index (within block) of y."""
    b, c = [i for i in range(3) if i != a]
    sub = {Z[block[a]]: y, Z[block[b]]: al*T, Z[block[c]]: be*T}
    G = sp.expand(F.subs(sub))
    # reduce with alpha^6 -> 1 - beta^6
    G = sp.expand(G.subs(al**6, 1 - be**6))
    Gs = sp.expand(G.subs({y: T, T: y}, simultaneous=True))
    return sp.expand(G - Gs) == 0, sub
for r in idx['records']:
    if r['status'] == 'solved':
        continue
    rec = json.load(open(root + r['path']))
    F = sp.sympify(rec['F']['expression'], locals=loc)
    A = sp.sympify(rec['A']['expression'], locals=loc)
    hits = []
    for block in ([3,4,5], [0,1,2]):
        for a in range(3):
            ok, sub = symmetric_after_cover(F, block, a)
            if ok:
                hits.append((['Y','X'][block==[0,1,2]], a))
    print(f"{r['id']:30s} q={rec['q']} A={rec['A']['expression']:28s} covers={hits}")
