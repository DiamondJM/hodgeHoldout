"""Combinatorial preconditions for the coset-restricted controlled reduction on T: u^3 + H = 0.
Points are (b,c,d,u) >= 0 with b+c+d+2u <= 6k (level k).  M' = {c+d even, u = 0 mod 3};
coset (par, r) = {c+d = par mod 2, u = r mod 3}."""
import itertools
def level_points(k, par, r):
    out = set()
    for u in range(r, 3*k + 1, 3):
        m = 6*k - 2*u
        for c in range(m + 1):
            for d in range(m - c + 1):
                if (c + d) % 2 != par: continue
                for b in range(m - c - d + 1): out.add((b, c, d, u))
    return out
ring = {k: level_points(k, 0, 0) for k in range(0, 8)}
R1 = sorted(ring[1])
print('ring points per level:', [len(ring[k]) for k in range(6)])
# ring generated in degree 1 (needed for peeling monomials of f^j): every point of level k >= 1 is (level k-1) + (level 1)
ok = all(any(tuple(x - y for x, y in zip(w, v)) in ring[k-1] for v in R1) for k in range(1, 8) for w in ring[k])
print('ring: every level-k point is a level-(k-1) point plus a level-1 ring point (k <= 7):', ok)
for par, r in ((1, 1), (1, 2), (0, 1), (0, 2), (1, 0)):
    mod = {k: level_points(k, par, r) for k in range(0, 8)}
    gen = all(any(tuple(x - y for x, y in zip(w, v)) in mod[k-1] for v in R1) for k in range(2, 8) for w in mod[k])
    # interior points (strict inequalities, all coordinates >= 1 and b+c+d+2u < 6k)
    inter = [sum(1 for (b, c, d, u) in mod[k] if min(b, c, d, u) >= 1 and b + c + d + 2*u < 6*k) for k in range(1, 5)]
    print(f'coset (c+d={par} mod 2, u={r} mod 3): points per level {[len(mod[k]) for k in range(6)]}, '
          f'generated over the ring from level 1 (k <= 7): {gen}, interior points levels 1..4: {inter}')
