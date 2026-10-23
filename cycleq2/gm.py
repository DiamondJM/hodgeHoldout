"""Fibrewise Griffiths-Dwork on eta^2 = f(xi) = xi^3 + a xi + b over K = Q(t):
reduce h(xi) dxi / eta^(2k+1) to the basis w0 = dxi/eta, w1 = xi dxi/eta; Gauss-Manin d/dt."""
import sympy as sp
t, xi = sp.symbols('t xi')

class Fibre:
    def __init__(self, a, b):
        self.a, self.b = sp.sympify(a), sp.sympify(b)
        self.f = xi**3 + self.a*xi + self.b
        self.fp = sp.diff(self.f, xi)
        # Bezout: u f + w f' = 1 over Q(t)[xi]
        s_, t_, g = sp.gcdex(sp.Poly(self.f, xi, domain='QQ(t)' if self.a.has(t) or self.b.has(t) else 'QQ'),
                               sp.Poly(self.fp, xi, domain='QQ(t)' if self.a.has(t) or self.b.has(t) else 'QQ'))
        self.u, self.w = (s_.as_expr()/g.as_expr()), (t_.as_expr()/g.as_expr())

    def reduce(self, h, m):
        """class of h dxi / eta^m (m odd) as (c0, c1) with h dxi/eta^m == c0 w0 + c1 w1."""
        h = sp.expand(h)
        while m > 1:
            # h = (h u) f + (h w) f'  ->  h/eta^m == (h u)/eta^(m-2) + (2/(m-2)) d/dxi(h w)/eta^(m-2)
            hu = sp.rem(sp.expand(h*self.u), self.fp, xi) if False else sp.expand(h*self.u)
            hw = sp.expand(h*self.w)
            # keep degrees small: reduce hw modulo f (adding multiples of f changes hu correspondingly)
            q, r = sp.div(sp.Poly(hw, xi), sp.Poly(self.f, xi))
            hw = r.as_expr(); hu = sp.expand(hu + q.as_expr()*self.fp)
            h = sp.expand(hu + sp.Rational(2, m-2)*sp.diff(hw, xi))
            h = sp.expand(sp.together(h)) if h.has(t) else h
            m -= 2
        # now h dxi/eta: use d(xi^k eta) = (k xi^(k-1) f + xi^k f'/2) dxi/eta == 0 to kill degree >= 2
        P = sp.Poly(sp.together(h), xi)
        h = sp.expand(sp.together(h))
        while True:
            P = sp.Poly(h, xi); d = P.degree()
            if d < 2: break
            k = d - 2
            rel = sp.expand(k*xi**(k-1)*self.f + xi**k*self.fp/2) if k > 0 else sp.expand(self.fp/2)
            lc = P.LC() / sp.Poly(rel, xi).LC()
            h = sp.expand(h - lc*rel)
        P = sp.Poly(h, xi)
        return sp.together(P.coeff_monomial(1)), sp.together(P.coeff_monomial(xi))

    def gauss_manin(self):
        """matrix G with d/dt (w0, w1) == G-columns: d/dt w_j = G[0,j] w0 + G[1,j] w1."""
        ft = sp.diff(self.f, t)
        cols = [self.reduce(-sp.Rational(1, 2)*xi**j*ft, 3) for j in (0, 1)]
        return sp.Matrix([[cols[0][0], cols[1][0]], [cols[0][1], cols[1][1]]])

if __name__ == '__main__':
    # sanity: constant curve, reduction identities
    E = Fibre(-1, 0)
    print(E.reduce(1, 3), E.reduce(xi, 3))
