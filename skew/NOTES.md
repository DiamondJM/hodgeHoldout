# one-reflection-skew: structural notes (exploration, not results for the site)

F = X0^6+X1^6+X2^6+Y0^6+Y1^6+Y2^6 + (X0^3X1+X1^3X2) p + (1/7) X0X1 p t,  A = X0^3 Y0^3, q = 1,
with p = Y0Y1, t = Y0^2-Y1^2, s = Y0^3-Y1^3, S = Y0^3+Y1^3, T = Y2^3.

## Surviving linear symmetries
Diagonal: tau (Y -> -Y), sigma (X1,Y1 -> -X1,-Y1), mu6 on Y2.  Y0<->Y1 and Y0 -> -Y1 (the hidden
reflections of one-reflection) negate the skew term; no diagonal X-twist repairs this
(it would need a+b = 3, 3a+b = 0 mod 6, impossible by parity).  sigma still splits
A = A+ + A-, A+- = X0^3 (Y0^3 +- Y1^3)/2, exactly as in fqlx's one-reflection proof.

## Fermat cover T^6 = Y0^6+Y2^6 (holdout / y2-sector)
The scaled exchange (y,T) -> (lam T, y/lam) preserves the skew image only if lam^2 = -alpha^2 and
lam^6 = 1, i.e. alpha^6 = -1: a constant, not the generic point of the Fermat curve.

## fqlx's cubic-surface (Hessian) reduction cannot absorb the skew term
Any reduction F = G(u, l1, l2, l3) with u = X0^2, passive X-ratios, and weight-2 Y-coordinates
l_i needs  p in span(l),  p t in Sym^2(l),  Y0^6+Y1^6+Y2^6 in Sym^3(l),  det d(l) ~ Y0^3 (or S, s).
 * If two of the l_i are free of Y2, the mu6 action on Y2 forces the third coordinate's orbit to have
   size <= 3, so the map factors through Y2^2 or Y2^3 and det picks up the wrong Y2 character.
   (This kills every choice with l = (p, t, *), e.g. l3 = m + Y2^6/(t^2+p^2), m = Y0^2+Y1^2,
   which does give a cubic surface  a u^3 + b u^2 p + (r/7) u p t + l3 (t^2+p^2)  but det ~ Y2^5.)
 * With l = (p, v=Y2^2, z=W/Y2) (fqlx's shape, W any Y0,Y1-cubic, even allowing W -> W + u L):
   p t is not in Sym^2, and W^2 + K(p) = Y0^6+Y1^6 forces W = Y0^3 +- Y1^3.
 * Product shape l2 l3 = p t - c p^2 with l2 a Laurent monomial in Y2 (k = 1, 2, 3) fails;
   a Y2-polynomial l2 gives det ~ (dl2/dY2)/l2, never Y2-free; the rank-one shape
   p t - c p^2 = m'^2 + p n' forces m' affine in Y2 and then C_003 ~ p^3/alpha^6, impossible.
The remaining product case is closed by the following argument (proof sketch, see below).

## No cubic-surface reduction with one active X-coordinate (general product case)
Setting: l1 = p, l2 l3 = P4 := p t - c p^2 (the nondegenerate case after shifting l2, l3 by
multiples of p), K := Y0^6+Y1^6+Y2^6 = C(p, l2, l3) with C a cubic over the field of the passive
ratios, and l2, l3 rational in Y2 over k = C(r,w)(Y0,Y1).
1. Substituting l3 = P4/l2 gives  Y2^6 = Phi(l2),  Phi(X) = sum_{j=0..6} E_j X^(j-3) - K0,
   where E_j are polynomials in p, P4 and K0 = Y0^6+Y1^6.  Phi is a Laurent polynomial: its only
   poles on P^1 are 0 and infinity.
2. Y2 -> Y2^6 = Phi(l2(Y2)) has a single pole, totally ramified.  l2 : P^1 -> P^1 is surjective, so if
   Phi had poles at both 0 and infinity, both would have preimages, giving two poles of Y2^6.
   Hence Phi has one pole; say infinity (the case 0 is the same with l2 <-> l3).  Then
   l2^{-1}(infinity) = {Y2 = infinity}, i.e. l2 is a polynomial in Y2 of degree 6/deg(Phi) >= 2.
3. p and P4 do not involve Y2, so  det d(p, l2, P4/l2)/d(Y0,Y1,Y2) = -(dl2/dY2) J(p,P4) / l2,
   and (dl2/dY2)/l2 depends on Y2 for every nonconstant polynomial l2.  But the density condition
   needs det_Y proportional to Y0^3 (or Y0^3 +- Y1^3), which does not involve Y2.  Contradiction.
(The X-part of the Jacobian splits off because u, r, w involve only X; the density must be
const * u^2 by separate X/Y weights, so det_Y must equal const * Y0^3.)
Groebner checks (Singular 4.3, char 32003, Y0=2, Y1=3; groebner/):
 * lemma_mobius.sing: l2 = (a0+a1 y)/(1+b1 y), saturated by b1 and by a1-a0 b1 -> ideal <1>
   (no non-polynomial Moebius l2); degree-1 polynomial l2 -> ideal <1> (needs degree >= 2).
 * control_poly2.sing: polynomial degree-2 l2 -> nonempty variety (the setup is not vacuous; these
   solutions are then killed by the Jacobian step 3).
 A degree-(2,2) rational ansatz exceeded 9 GB in the first saturation and was abandoned.

## Fixed-denominator calibration on the solved one-reflection
Supports s^2+T^2, S^2+T^2, T^2 - s^2/3, T^2 - S^2/3 (degree 6): A, A+, A- all NOT supported
(mod 268435399).  The accepted support is the degree-30 D+ = 9 delta Z + 4 h^3 T^2, so low-degree
fixed-D tests are weak evidence on this family.

## Option 3 (first-order deformation of fqlx's certificate): sizing
fqlx_cert.py rebuilds fqlx's strict half-certificate (N+, D+) mod 268435009 (a prime with sqrt 3)
and checks N+(F0) = A+ D+ and D+ div N+ - N+(D+) = 0 exactly.  D+ has 725 terms, N+ 352-546
per component, N+(Kskew) 1590.  The skew sextic keeps only 24 diagonal symmetries (vs 216), and
D+ is semi-invariant only under tau (the powers of T = Y2^3 are mixed through R = T + lam s/3), so
the first-order system for (N1, D1, H) after the tau split is ~1.13M + 2*0.16M unknowns against
~4.1M rows of degree 60, with ~1.5k nonzeros per numerator column: out of reach for dense or
Python-level sparse elimination on this machine.
Side remark: the degree-6 test showed s^2+T^2 does not support A+-, so fqlx's support is not
the tritangent-plane curves {u = rho_k p, s = +-i T}; those curves do deform to first order in the
skew fibers (Kskew restricted to them lies in (u - rho p, s, T, p^2)), but that is not the relevant support.

## Route 2: fibration over (r, w, x = Y0/Y1)  (skew/fibration.py)
Fibre = plane sextic g(X0^2, Y1^2) + Y2^6 = 0, g a binary cubic; the skew term only adds
(r/7) x (x^2-1) U V^2 to g, so it is harmless here, and the picture is identical for one-reflection.
The residue character of A under (X-block sign, (Y0,Y1) sign, Y2 -> zeta Y2) is (+1, -1, zeta);
on the fibre this is the 2-dim eigenspace {X0 Y1^2, X0^3} of H^{1,0} with no (0,1) part: a
signature-(2,0) unitary piece of a mu6-cover of P^1, not an elliptic curve.  So the elliptic-companion
library does not apply directly, and this fibration neither obstructs nor serves.
