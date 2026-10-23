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

## Triple-cover Jacobian model (model_check.py, triple_cover.py)
cycle-q2 has the same sextic as cycle-three, so hodgepodgeconjecture's Jacobian model applies:
  M1:  256 y^2 = 256 x^3 + 32 a8(c1,c2,1,r,t) x + b256(c1,c2,1,r,t),   t/r = v^6, v = Y0/X0,
with c1 = (Y1/X1)/v, c2 = (Y2/X2)/v passive (a8, b256 from data/cycle-three/JacobianModel.lean).
Check: for 12 random (v,c1,c2) mod 101, 103, 107 the physical plane cubic (cycle-three's chart) and
M1 have equal point counts, so M1 is the Jacobian family (not a quadratic twist).
In (r:t), a8 and b256 are forms of degree 4 and 6: M1's fibres over fixed (c1,c2) are RATIONAL
elliptic surfaces (chi = 1, p_g = 0), consistent with cycle-three's all-polynomial-sources theorem.

Triple cover M3: base change (r:t) = (rho^3 : tau^3), tau/rho = v^2 (i.e. adjoin T3 = R v^2):
  M3:  256 y^2 = 256 x^3 + 32 a8(c1,c2,1,rho^3,tau^3) x + b256(c1,c2,1,rho^3,tau^3)  in P(1,1,6,9).
a, b have degrees (12, 18); orders at rho = 0 are (6, 0) and at tau = 0 are (3, 0), so the model
is minimal: chi = 3, p_g = 2.  j is nonconstant (checked at c1,c2 = 2,3), so not isotrivial.
H^{2,0} = {dtau ^ dx/y, tau dtau ^ dx/y}: deck tau -> omega tau acts by omega and omega^2, so the
invariant part is M1's (p_g = 0) and each nontrivial sector has h^{2,0} = h^{0,2} = 1.

Why the target needs M3: M1's volume multiplier (cycle-three's density_multiplier) is -144 R v^3,
which matches the q=1 target's v^3.  The q=2 target A = alpha^2 beta^2 gamma U^2V^2W^2
= v^5 c1^2 c2 R^6 x^2 y^2 carries v^5, an extra v^2 = T3/R that is a function on M3 but not on M1.
On M3 the density then lies in a nontrivial deck sector.

Consequence: on M3 the analogue of cycle-three's "every polynomial source has a primitive" is
FALSE.  The nontrivial sectors contain transcendental classes (h^{2,0} = h^{0,2} = 1 per fibre).
A construction must show that the transported q=2 source has zero component along that piece,
over the (c1,c2) family, or deal with it.
Next step: derive the pole-two transport (second variation in cycle-three's jet calculus) and test
the resulting model source against the H^{2,0} representatives by Griffiths reduction on M3.

## Step 1: pole-two transport, cohomological form (invariants.py, inv_check.py, second_variation.py)
Exact identity of forms:  2 A Omega/F^3 = d_s1 d_s2 (Omega/F_s)|_{s=0},
  F_s = F + s1 m1 + s2 m2,  m1 = X0X1X2Y0Y1Y2 = alpha beta gamma UVW,  m2 = X0X1X2^2Y0Y1 = alpha beta UVW,
since m1 m2 = A.  Both directions add an xyz term to cycle-three's cubic, with coefficients
g1 = v^3 c1 c2 and g2 = v^2 c1 in its chart.

Invariants with an xyz term (Hessian syzygy H(H(U)) = lam U + mu H(U), normalised to cycle-three):
  48 s4 = 48(ae^2f + bdf^2 + cd^2e) + 216 abc m - 24 def m - m^4,
  216 s6 = 5832a^2b^2c^2 + 864a^2ce^3 + 864ab^2f^3 + 1296abcdef - 540abc m^3 - 864abef^2 m - 864acde^2 m
           + 72ae^2f m^2 + 864bc^2d^3 - 864bcd^2f m + 72bdf^2 m^2 + 72cd^2e m^2 - 216d^2e^2f^2 - 36def m^3 - m^6,
  Jacobian: eta^2 = xi^3 + s4 xi - s6/4.  Checked: equal point counts for 20 random cubics (with m != 0)
  mod 101, 103, 107, 109, no mismatch.

Variations at s = 0 (A = s4, B = -s6/4):  A1, B1 carry v^3; A2, B2 carry v^2; A12 = 0; B12 carries v^5
(all mod 6, everything else is a function of t = v^6).  Gauss-Manin on the model:
  d_s1 d_s2 [dX/Y] = [ 3(A1 X + B1)(A2 X + B2)/(4 Y^5) - (A12 X + B12)/(2 Y^3) ] dX,
and Res(Omega/F) = (model form)/(-144 R v^3) (cycle-three density_multiplier).  Writing A1 = v^3 A1~,
A2 = v^2 A2~, B12 = v^5 B12~ (tilde quantities functions of t on M1), the transported q=2 source is
  S = -(1/288) (v^2 / R) [ 3(A1~ X + B1~)(A2~ X + B2~)/(4Y^5) - B12~/(2Y^3) ] dT dc1 dc2 dR dX,
with v^2 = T3/R: a rational source on the triple cover M3 in a nontrivial deck sector, and NOT on M1.
This confirms (now from the actual Weierstrass variations, not a heuristic) that the target needs M3.

Caveats (needed for a proof, not for the cohomology computation):
 * the multiplier -144 R v^3 is assumed independent of s.  T, c1, c2, R do not move with s; it comes
   from cycle-three's covariant identity D_y xi/(2 eta) = 3/g, which holds for every ternary cubic.
   This should still be re-derived with the xyz term;
 * the moving map (covariants X, Y depend on s) contributes exact corrections at first and second
   order.  cycle-three's first-order correction W generalises, but the second-order term must be
   written out explicitly for a certificate.

Step 2 (next): S restricted to a fibre over fixed (c1,c2) is a class sigma on the elliptic surface
S3 (chi = 3, p_g = 2).  The certificate route survives iff sigma has no (0,2) part.  sigma lies in the
omega-sector, so this is the vanishing of the cup product of sigma with the holomorphic 2-form of the
omega^2-sector.  That is computable by Griffiths reduction on the weighted surface mod p.
