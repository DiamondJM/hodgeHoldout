"""The transported q=2 source sigma at a base point, as a vector in the target-sector normal-form frame.
sigma = Res(P Omega/G^3) + Res(P' Omega/G^2),  P = 12 tau^3 (A1~ x + B1~)(A2~ x + B2~),  P' = 6 tau^3 B12~,
using Res(h Omega/G^k) = c_k h dtau dx / y^(2k-1), c_2 = -1/4, c_3 = 3/16 (overall constant dropped)."""
import sympy as sp, pickle, functools
from gm_engine import P as PR, inv, mul, add, scal, ratmod
from gm_jets import JetPoint
rho, tau, x, v, c1, c2, t = sp.symbols('rho tau x v c1 c2 t')

@functools.lru_cache(None)
def tables():
    D = pickle.load(open('/home/user/hodgeHoldout/cycleq2/variation.pkl', 'rb'))
    def as_t(expr, vpow): return sp.expand(sp.expand(expr / v**vpow).subs(v, t**sp.Rational(1, 6)))
    q = {k: as_t(D[k], p) for k, p in (('A1', 3), ('B1', 3), ('A2', 2), ('B2', 2), ('B12', 5))}
    Pt = sp.expand(12*tau**3*((q['A1']*x + q['B1'])*(q['A2']*x + q['B2'])).subs(t, tau**3))
    Ppt = sp.expand(6*tau**3*q['B12'].subs(t, tau**3))
    def homog(expr, deg):
        out = {}
        for (i, k, l1, l2), cf in sp.Poly(expr, tau, x, c1, c2).terms():
            r = deg - i - 6*k
            assert r >= 0
            out[(r, i, k, l1, l2)] = ratmod(cf)
        return out
    return homog(Pt, 37), homog(Ppt, 19)

def at_point(tab, cc):
    out = {}
    for (r, i, k, l1, l2), cf in tab.items():
        val = cf * pow(cc[0], l1, PR) % PR * pow(cc[1], l2, PR) % PR
        if val: out[(r, i, k)] = (out.get((r, i, k), 0) + val) % PR
    return out

def sigma_vec(cc, pt=None, fr=None):
    if pt is None: pt = JetPoint(cc, 0)
    if fr is None:
        fr = []
        for kp in (1, 2, 3): fr += [(kp, mm) for mm in pt.setup(18*kp - 17, 0)[4]]
    index = {(18*k - 17, mm): n for n, (k, mm) in enumerate(fr)}
    t37, t19 = tables()
    vec = [0]*len(fr)
    for tab, kp in ((t37, 3), (t19, 2)):
        red = pt.reduce({(0, 0): at_point(tab, cc)}, kp, 0)
        for key, jets in red.items(): vec[index[key]] = (vec[index[key]] + jets.get((0, 0), 0)) % PR
    return fr, vec

if __name__ == '__main__':
    for cc in ((2, 3), (3, 5)):
        fr, s = sigma_vec(cc)
        print(cc, 'sigma =', s)
