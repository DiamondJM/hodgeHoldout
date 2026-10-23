# cycle-q2: does holdout-q2's line construction port?  (structure.py)

F = sum Z^6 + (1/2)(X0^3X1Y0Y1 + X0X2^3Y0Y2 + X1^3X2Y1Y2), q = 2, A = X0^2X1^2X2^3Y0^2Y1^2Y2.

## Paired-ratio cubic
With alpha = Y0/X0, beta = Y1/X1, gamma = Y2/X2 passive and U, V, W = X0^2, X1^2, X2^2 active:
  F = (1+alpha^6)U^3 + (1+beta^6)V^3 + (1+gamma^6)W^3 + (1/2)(alpha beta U^2V + beta gamma V^2W + alpha gamma UW^2),
  A = alpha^2 beta^2 gamma U^2 V^2 W^2,  and each pair map (X, Y) -> (X^2, Y/X) has Jacobian 2.
So F is a family of plane cubics (elliptic curves) over a 3-dimensional base, not a cubic surface.

## Why the holdout-q2 reduction has no analogue
holdout-q2 keeps the endpoint pair (c, d) active through S = c^2 + k^2 d^2, T = kcd, which works
because c, d enter F only through cd and c^6 + d^6.  In the cycle every pair enters through both
Z W and Z^3 W (e.g. X1^3X2Y1Y2 and X0X2^3Y0Y2 for pair 2), so no pair can stay active with
weight-2 coordinates: X2Y2 and X2^3Y2 need X2^2 too, and then X2^6 + Y2^6 is not cubic.
Keeping (X2^2, X2Y2, Y2^2) gives a (2,3) complete intersection fibre, a K3 surface (p_g = 1).
There is no cubic surface, hence no 27-line algebra to port.

## Character
Diagonal symmetry group of F: 72 modulo scalars.  The residue character of A is zeta^{0,2,4}
(computed for every element): trivial on an index-3 subgroup of order 24 (it contains tau and every
paired sign), and a primitive cube root of unity on the quotient mu3.
CORRECTION: an earlier version said cycle-three's Jacobian model is a quotient killing this mu3.
That is wrong: under g = (0,2,0,2,2,4) its passive coordinates c1 = (Y1/X1)/v, c2 = (Y2/X2)/v pick up
zeta^-2, zeta^2, so the model is not that quotient.  Whether that route can reach this character
is open; its transport is a first-variation identity built for q = 1.

## What a construction would need
1. A primitive theorem on a model that reaches the omega-isotypic sector (an elliptic-family model
   compatible with the mu3 action), with its own seed / lifting / trace argument.
2. Pole order two: downstairs the source has degree 6 on a plane cubic (R_6 = 0), so it reduces to
   lower pole order plus base derivatives, i.e. a second variation; the shared HigherResidues
   library (split-ternary) handles a related third-order-pole calculus.
Both are new mathematics plus a cycle-three-sized Lean development; not a port.
