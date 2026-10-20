import mpmath as mp
mp.mp.dps = 50
def data(r, branch=0):
    m = r**4-4*r**3+5*r**2+r-2
    R = r*(1-r-r**2)/(1-r); M = r**2*m/(r-1)**2
    a = 3*(1-2*r)/(1-r); b = 3*(1-2*r)
    return m,R,M,a,b
def check(r, k, q):
    m,R,M,a,b = data(r)
    p = r/q; al = a/(k*q); be = b/(k**3*q)
    # H(phi) coefficients: expand numerically on a grid via polynomial fit: evaluate at s=1, several t
    def H(s,t):
        X0,X1,X2 = s**2, k*s*t, t**2
        S = -(s**4+q**2*s**2*t**2+t**4); P = p*s**3*t+q*s*t**3
        return X0**6+X1**6+X2**6 + P*(al*X0**3*X1+be*X1**3*X2) + S**3-3*S*P**2
    vals = [abs(H(1, mp.mpc(0.3*j, 0.1*j+0.2))) for j in range(1,6)]
    return max(vals), al, be
# fqlx seed: r in (7,8) root of f with q^4=R, k^6=M/q^2 (any branches)
import sympy as sp
rr = sp.symbols('r')
f = sp.sympify("r**23-14*r**22+86*r**21-290*r**20+520*r**19-199*r**18-94566*r**17+1029405*r**16-5018220*r**15+13903481*r**14-22713424*r**13+17780092*r**12+9399696*r**11-47299809*r**10+72791853*r**9-73173409*r**8+54302525*r**7-30776930*r**6+13325391*r**5-4325886*r**4+1016955*r**3-163296*r**2+16038*r-729")
r_f = [complex(z) for z in sp.Poly(f, rr).nroots(n=30) if abs(sp.im(z))<1e-20 and 7<sp.re(z)<8][0].real
r_f = mp.mpf(r_f)
m,R,M,a,b = data(r_f)
q = R**(mp.mpf(1)/4); k = (M/q**2)**(mp.mpf(1)/6)
mx, al, be = check(r_f, k, q)
print("fqlx seed: max|H(phi)| =", mp.nstr(mx,5), " alpha^6+beta^6 =", mp.nstr(al**6+be**6,20))
# generic r: does the conic lie on H for every r?
r0 = mp.mpf('2.37')
m,R,M,a,b = data(r0); q = R**(mp.mpf(1)/4); k = (M/q**2)**(mp.mpf(1)/6)
print("generic r=2.37: max|H(phi)| =", mp.nstr(check(r0,k,q)[0],5))
# one-reflection seed: root of g, with k^2 = 1-r and q^2 = M/(1-r)^3
g = sp.sympify("r**8 + 7*r**7 - 58*r**6 + 149*r**5 - 178*r**4 + 115*r**3 - 44*r**2 + 10*r - 1")
for z in sp.Poly(g, rr).nroots(n=40):
    r0 = mp.mpc(complex(z))
    m,R,M,a,b = data(r0)
    k = mp.sqrt(1-r0); q = mp.sqrt(M/(1-r0)**3)
    mx, al, be = check(r0, k, q)
    print("g-root r =", mp.nstr(r0,12), " max|H(phi)| =", mp.nstr(mx,5), " |alpha-beta| =", mp.nstr(abs(al-be),5), " alpha =", mp.nstr(al,10), " q^4-R =", mp.nstr(abs(q**4-R),5))
