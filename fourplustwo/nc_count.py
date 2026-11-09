import numpy as np, sys, time
from multiprocessing import Pool
def run(seed):
    import normcontact as nc
    rng = np.random.default_rng(seed); tv = 0.37 + 0.21j; out = []
    for _ in range(250):
        x0 = rng.normal(size=len(nc.unk)) + 1j*rng.normal(size=len(nc.unk))
        x, nr, it = nc.newton(x0, tv, iters=120)
        if nr < 1e-11: out.append(x)
    return out
if __name__ == '__main__':
    t0 = time.time()
    with Pool(4) as p: res = p.map(run, range(100, 116))
    sols = [x for r in res for x in r]
    # distinct up to tolerance
    keys = {}
    for x in sols:
        k = tuple(np.round(x[:6], 5))
        keys[k] = keys.get(k, 0) + 1
    n, dn = len(sols), len(keys)
    pairs = sum(v*(v-1)//2 for v in keys.values())
    est = n*(n-1)/2/pairs if pairs else float('inf')
    print(f'{n} convergences, {dn} distinct, {pairs} coincident pairs -> estimated number of solutions ~ {est:.0f}  ({time.time()-t0:.0f}s)')
    np.save('nc_solutions.npy', np.array([np.array(x) for x in sols]))
