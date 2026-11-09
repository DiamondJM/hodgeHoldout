"""Scan F_p^2 for base points where Kodaira-Spencer on the target-sector holomorphic 2-form degenerates:
rank{s, nabla_1 s, nabla_2 s} < 3 (a curve of such points, tangent to the kernel, could carry (3,1) support)."""
import sys, os
from multiprocessing import Pool
from flint import nmod_mat
def work(c1v):
    from gm_engine import P
    from gm_jets import connection_jets
    out = []
    for c2v in range(1, P):
        try:
            fr, Gam = connection_jets((c1v, c2v), 0)
        except Exception as e:
            out.append((c1v, c2v, 'bad')); continue
        N = len(fr)
        if N != 12: out.append((c1v, c2v, 'frame%d' % N)); continue
        s = [n for n, (k, m) in enumerate(fr) if k == 1][0]
        W = nmod_mat(N, 3, P); W[s, 0] = 1
        for i in (0, 1):
            for r in range(N): W[r, 1 + i] = Gam[i][(0, 0)][r, s]
        rk = W.rank()
        if rk < 3: out.append((c1v, c2v, rk))
    return out
if __name__ == '__main__':
    from gm_engine import P
    with Pool(4) as pool:
        res = pool.map(work, range(1, P), chunksize=1)
    flat = [x for r in res for x in r]
    bad = [x for x in flat if isinstance(x[2], str)]; deg = [x for x in flat if not isinstance(x[2], str)]
    print(f'p={P}: {(P-1)**2} points, {len(bad)} singular/bad, {len(deg)} with KS rank < 3 on s')
    print('degenerate points:', deg[:60])
    import pickle; pickle.dump((bad, deg), open(f'ks_scan_{P}.pkl', 'wb'))
