# Fixed-denominator sweep over the open instances (modular evidence, p = 268435399)

For each open instance, `fixed_d.py` tests natural degree-6 denominators D (sums of 2-4 sixth powers,
and every coordinate sub-equation of F containing a coupling): is the full cleared system
A D^2 - q D N(F) + F (D div N - N(D)) = F^(q+1) Q solvable for (N, Q)?  Controls: the Fermat join
D = X0^6+X1^6+X2^6 serves X0^3 Y0^3; X1^6+X2^6+Y1^6 does not.

| instance | candidates | solvable |
|---|---|---|
| cycle-q2 | 59 | not run (dense q=2 system exceeds memory) |
| cyclic-triple-residual | 71 | 0 |
| dense-rational | 106 | 0 |
| diagonal-permutation | 77 | 0 |
| eight-plane-configuration | 106 | 0 |
| four-plus-two-residual | 86 | 0 |
| klein-coupled-character | 53 | 0 |
| off-paired | 57 | 0 |
| one-reflection-skew | 55 | 0 |
| polarized-k3-remainder | 100 | 0 |
| quadratic-cubic-pullback | 97 | 0 |
| quadric-contact-residual | 79 | 0 |
| rank-one-biquartic | 101 | 0 |
| reflection-coupled-residual | 61 | 0 |
| short-power-presentation | 106 | 0 |
| symmetric-sextic-residual | 65 | 0 |

No degree-6 natural support carries the target for any q=1 open instance. On the solved one-reflection the accepted support has degree 30, so these negatives are weak evidence.
