"""Check cycle-three's Weierstrass model against the physical cubics by point counts mod p,
then examine its triple base change (r:t) = (rho^3 : tau^3), tau/rho = v^2."""
import random, sympy as sp

def a8(c1, c2, al, r, t):
    return r**2*t*(c1**2*c2**3*(al*r+t) + c1*c2**2*(r+c1**6*t) + c1**3*c2*(r+c2**6*t))
def b256(c1, c2, al, r, t):
    return (-1728*(al*r+t)**2*(r+c1**6*t)**2*(r+c2**6*t)**2
            - 32*r**2*t*(c1**3*c2**3*(al*r+t)**2*(r+c2**6*t) + c2**3*(al*r+t)*(r+c1**6*t)**2
                         + c1**3*(r+c1**6*t)*(r+c2**6*t)**2)
            - 48*r**2*t*c1**2*c2**2*(al*r+t)*(r+c1**6*t)*(r+c2**6*t)
            + r**4*t**2*c1**4*c2**4)

def count_cubic(co, p):
    a, b, c, d, e, f = co
    G = lambda x, y, z: (a*x**3 + b*y**3 + c*z**3 + d*x*x*y + e*y*y*z + f*z*z*x) % p
    n = sum(1 for x in range(p) for y in range(p) if G(x, y, 1) == 0)
    n += sum(1 for x in range(p) if G(x, 1, 0) == 0) + (1 if G(1, 0, 0) == 0 else 0)
    return n

def count_weier(A, B, p):   # 256 y^2 = 256 x^3 + 32 A x + B
    sq = {}
    for y in range(p): sq[y*y % p] = sq.get(y*y % p, 0) + 1
    inv256 = pow(256, p-2, p)
    return 1 + sum(sq.get((256*x**3 + 32*A*x + B) * inv256 % p, 0) for x in range(p))

if __name__ == '__main__':
  random.seed(1)
  for p in (101, 103, 107):
      for _ in range(4):
          v, c1, c2 = (random.randrange(1, p) for _ in range(3))
          h = pow(2, p-2, p)
          # physical cubic in x = X0^2/R, y = X1^2/R, z = 1 (cycle-three solution.md)
          co = (1+v**6, 1+c1**6*v**6, 1+c2**6*v**6, v*v*c1*h, v*v*c1*c2*h, v*v*c2*h)
          r, t = 1, pow(v, 6, p)
          A, B = a8(c1, c2, 1, r, t) % p, b256(c1, c2, 1, r, t) % p
          nc, nw = count_cubic([x % p for x in co], p), count_weier(A, B, p)
          print(f'p={p} v={v} c1={c1} c2={c2}: cubic {nc}, Weierstrass {nw}', 'OK' if nc == nw else 'MISMATCH')
