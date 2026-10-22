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
These are the cases I could close by hand; a general rational l2 with l2 l3 = p t - c p^2 is open.

## Fixed-denominator calibration on the solved one-reflection
Supports s^2+T^2, S^2+T^2, T^2 - s^2/3, T^2 - S^2/3 (degree 6): A, A+, A- all NOT supported
(mod 268435399).  The accepted support is the degree-30 D+ = 9 delta Z + 4 h^3 T^2, so low-degree
fixed-D tests are weak evidence on this family.
