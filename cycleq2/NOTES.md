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

## Step 2: (0,2) test by Griffiths reduction (gm.py, step2.py, solve_rational.py, degree_check.py,
##          jacobian_ring.py, ks_test.py)
Fibre surface S3 over fixed (c1,c2): G = y^2 - x^3 - a(rho,tau) x - b(rho,tau) in P(1,1,6,9), degree 18,
a = rho^12 A((tau/rho)^3), b = rho^18 B((tau/rho)^3).  Weighted Jacobian ring R = Q[rho,tau,x]/(G_rho, G_tau, G_x):
dim R_1 = 2 (= p_g), R_19 = 28, R_37 = 2 (= h^{0,2}), R_38 = 1 (socle), R_39 = 0, at (c1,c2) = (2,3), (3,5), (1,4).
The transported source is sigma = Res(P Omega/G^3) + Res(P' Omega/G^2), with
P = 3 tau^3 (3/4)(A1~ x + B1~)(A2~ x + B2~).  P has weighted degree 33 <= 37 and P' degree 9 <= 19,
so sigma is a class on the compact surface with no pole along the fibre at infinity, and its
(0,2)-component is [P] in R_37 (the pole-two term lies in F^1).
 * P is NOT in J_37 at all three points: fibrewise, sigma has a nonzero transcendental (0,2) part.
   (Consistently, the fibrewise Gauss-Manin equation G' + G/(3t) + M G = H has no rational solution
   with denominators t^j Delta^k, j <= 4, k <= 2, deg N <= 40; this test is too strict by itself because
   it ignores horizontal curves.)
 * But the 4-fold class is sigma ^ dc1 ^ dc2, and base Gauss-Manin terms (Kodaira-Spencer,
   multiplication by dG/dc_i : R_19 -> R_37) can absorb a (0,2) part.  dG/dc1 R_19 + dG/dc2 R_19
   spans all of R_37 at all three points, so P is in J_37 + KS.  No obstruction at the (0,2) level.
Conclusion: the triple-cover route is NOT ruled out at the Hodge-theoretic (0,2) level, but it cannot
be fibrewise.  A primitive must vary with (c1,c2), and its base derivatives must cancel the
transcendental part.  This is the c-direction analogue of cycle-three's first-variation identity;
cycle-three needed no such terms because p_g = 0 on its model.
Still open: the (1,1) level.  After the KS correction, the residual (1,1) part must be algebraic,
i.e. its transcendental (1,1) component must vanish modulo the next KS images (R_1 -> R_19 via dG/dc).
The full statement is a de Rham computation for the transcendental local system over the
(c1,c2)-plane.  Caveats from step 1 (s-independence of the multiplier, moving-map corrections) still apply.

## The (1,1) level (sectors.py)
Sector dimensions at (c1,c2) = (2,3) (sector of Res(Q Omega/G^k) = tau-exponent of Q + 1 mod 3):
  target sector omega: R_1 = 1, R_19 = 10, R_37 = 1  -> V_omega has Hodge numbers (1, 10, 1);
  omega^2 sector:      1, 10, 1;   invariant sector: 0, 8, 0 (the rational elliptic surface M1).
Kodaira-Spencer in the target sector: R_1 -> R_19 has image 2 (both base directions, injective);
R_19 -> R_37 has image 1 (onto, as in step 2).
So the transcendental sub-VHS T_omega generated by the holomorphic 2-form has Hodge numbers at least
(1, 2, 1).  If it is exactly that, NS_omega has rank at most 12 - 4 = 8.

Why there is no pointwise (1,1) test: at a single base point the c-derivatives of a correction
Theta = theta1 dc1 + theta2 dc2 can be prescribed freely (Poincare lemma on the 2-dimensional base).
So every F^1 leftover can be cancelled at a point; only the (0,2) symbol (step 2) gives a pointwise
condition.  The real (1,1)-and-above question is global: is Sigma in
  nabla(Omega^1_K (x) V_omega) + NS_omega (x) K,   K = C(c1,c2),
i.e. does Sigma vanish in de Rham cohomology over the generic point of the base, modulo algebraic
classes?  Removing curves from the base cannot kill classes such as dlog f ^ dlog g (x) section, so
this is a genuine rational-integrability (creative-telescoping) problem.  It concerns the rank-12
Gauss-Manin system of V_omega over Q(c1,c2), or its rank >= 4 transcendental quotient.
Next computational step: derive that Gauss-Manin system by Griffiths reduction over Q(c1,c2) (or by
jets at a point), find T_omega as the D-module generated by the holomorphic 2-form, and search for
rational Theta solving nabla Theta = Sigma modulo NS.

## Rank of the transcendental part (dmodule_rank.py)
Span of nabla^alpha s, s = Res(rho Omega/G) (the target-sector holomorphic 2-form), derivatives in
c1, c2 tracked formally through d^beta G, then Griffiths-reduced to normal form at (c1,c2) = (2,3):
  order 0: rank 1;  order <= 1: rank 3;  order <= 2: rank 4;  order <= 3: rank 4;  order <= 4: rank 4.
The span is closed under nabla from order 2 on, so s generates a rank-4 sub-local system T_omega of
the 12-dimensional V_omega, with Hodge numbers (1, 2, 1).  This is the minimum allowed by the KS ranks.
So the target sector is V_omega = T_omega (rank 4) + an 8-dimensional complement, which should be
NS_omega (algebraic) if V_omega splits as T + NS.  The global question for cycle-q2 reduces to a
rank-4 Gauss-Manin system over Q(c1,c2): is the image of Sigma in H^2_dR(K, V_omega / NS_omega) zero?
Equivalently, does Sigma pair to zero, after rational integration, with the rank-4 dual system T_{omega^2}?
