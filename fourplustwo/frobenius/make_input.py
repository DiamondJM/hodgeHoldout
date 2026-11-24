"""Input line for ToricControlledReduction (Costa-Harvey-Kedlaya): the core threefold
T: u^3 + H(a,b,c,d) = 0 in P(1,1,1,1,2), chart a = 1, torus coordinates (b, c, d, u), scaled by 7."""
import sys
p = int(sys.argv[1])
f = {(0,0,0,0): 7, (6,0,0,0): 7, (1,0,0,0): 5, (5,0,0,0): 10,          # a^6, b^6, (5/7)a^5 b, (10/7) a b^5
     (0,6,0,0): 7, (0,0,6,0): 7, (0,5,1,0): 5, (0,1,5,0): 15,          # c^6, d^6, (5/7)c^5 d, (15/7) c d^5
     (1,1,1,0): 5, (1,3,1,0): 10,                                      # (5/7) a^3 b c d, (10/7) a b c^3 d
     (0,0,0,3): 7}                                                     # u^3
A = [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1],[-1,-1,-1,-2]]; b = [0,0,0,0,6]
fmt = lambda x: str(x).replace(' ', '').replace('(', '[').replace(')', ']')
print(f"core_p{p}:{fmt(list(f.keys()))}:{fmt(list(f.values()))}:{fmt(A)}:{fmt(b)}:{p}")
