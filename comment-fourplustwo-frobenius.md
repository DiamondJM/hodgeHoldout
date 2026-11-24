Frobenius data for **four-plus-two-residual**, in reply to `Robertboy18`'s request for the characteristic polynomial of Frobenius on $H^3(T)^-$. Prepared with Claude Code assistance on behalf of `DiamondJM`. **No certificate, Lean proof, or solve PR is claimed.** Everything below is $p$-adic numerics, checked against point counts but not certified.

**Summary.** I could not get the full polynomial (item 4). What I could get answers the simplicity question at twelve primes at once: Frobenius is ordinary on $H^3(T)^-$, and the $p$-adic factorisation patterns leave no room for a proper nonzero deck-stable sub-object that is compatible with Frobenius.

**1. Setting.** $T:\ u^3+H=0$ in $\mathbb P(1,1,1,1,2)$, and $H^3(T)^-$ is the part odd under $(Y_0,Y_1)\mapsto(-Y_0,-Y_1)$, of rank 96. The deck group makes it a $\mathbb Q(\omega)$-vector space of rank 48. For $p\equiv1\pmod 6$ it splits over $\mathbb Q_p$ into two pieces $M_1,M_2$ (the deck characters), dual to each other. The program finds Hodge numbers $(h^{2,1},h^{1,2})=(32,16)$ for $M_1$ and $(16,32)$ for $M_2$.

**2. Method.** Controlled reduction in $p$-adic cohomology (Costa, Harvey and Kedlaya, *Zeta functions of nondegenerate hypersurfaces in toric varieties via controlled reduction in p-adic cohomology*, ANTS XIII), using Costa's implementation `ToricControlledReduction`. Unmodified, it needs more than 15 GB on $T$. The exponents of the equation lie in a sublattice of index 6, so I patched the library to work on one coset of that sublattice: the lattice points of one piece, with all reductions done in the invariant ring. Checks:
- on two curves with automorphisms of order 2 and 3, the product over the pieces equals the unpatched program's zeta polynomial;
- on $T$, the trace on the 96-dimensional part equals an independent point count: $133$ modulo $19^3$, $-155$ modulo $31^3$, and $134$ modulo $67^2$.

**3. Result.** At each of $p=19,31,37,43,61,67,73,79,103,109,127,139$ Frobenius on $M_1$ is ordinary, with slopes $1$ (16 times) and $2$ (32 times). These are all primes $p\equiv1\pmod6$ below 140 except 13 and 97, which the program rejects as degenerate. Degrees of the irreducible factors over $\mathbb Q_p$:

| $p$ | slope-1 part (degree 16) | slope-2 part (degree 32) |
|---|---|---|
| 19 | 1, 1, 7, 7 | 6, 9, 17 |
| 31 | 1, 15 | not squarefree mod $p$ |
| 37 | 16 | 1, 6, 25 |
| 43 | 1, 1, 2, 3, 9 | 1, 1, 5, 6, 7, 12 |
| 61 | 1, 2, 13 | 1, 6, 25 |
| 67 | 1, 6, 9 | 2, 3, 27 |
| 73 | 2, 3, 11 | 1, 3, 5, 23 |
| 79 | 1, 2, 6, 7 | 1, 2, 4, 12, 13 |
| 103 | 2, 4, 10 | 1, 3, 12, 16 |
| 109 | 1, 6, 9 | 12, 20 |
| 127 | 7, 9 | 1, 6, 25 |
| 139 | 2, 5, 9 | 1, 2, 11, 18 |

*Consequence.* Let $W\subset H^3(T)^-$ be a deck-stable sub-Hodge structure of geometric origin, so that Frobenius acts on it with characteristic polynomial in $\mathbb Q(\omega)[t]$ at each $p$. Write $(a,b)=(h^{1,2},h^{2,1})$ for its part in $M_1$. At an ordinary prime its slope-1 part has rank $a$ and its slope-2 part rank $b$. So $a$ is a sum of slope-1 degrees and $b$ a sum of slope-2 degrees, in every row of the table.
- $p=37$ gives $a\in\{0,16\}$. The rows $p=19,37,67$ give $b\in\{0,32\}$ (so do $109$ and $127$).
- $(a,b)=(16,0)$: every eigenvalue would have valuations $(1,2)$ at the two primes above $p$, hence equal $\pi\bar\pi^2$ times a root of unity (Kronecker), where $p=\pi\bar\pi$. That root of unity would have at most 16 conjugates over $\mathbb Q(\omega)$. But at $p=19$ there are factors of degree 7, and a root of unity of degree 7 over $\mathbb Q_{19}$ has at least 28 conjugates over $\mathbb Q(\omega)$.
- $(a,b)=(0,32)$: the same argument with the degree-17 factor at $p=19$ (at least 102 conjugates, against at most 32).

So $W=0$ or $W=H^3(T)^-$: the eigenspace is simple in this sense. If the sub-Hodge structure in the degree-6 argument above is of geometric origin, this excludes it. I have not checked that argument or its rank bounds, and the conclusion is conditional on the numerics.

The Hodge type is used. With the total rank alone, ranks $1,6,7,16$ and their complements survive all twelve primes.

**4. What is missing.** The exact characteristic polynomial. Recovering its coefficients in $\mathbb Z[\omega]$ needs about ten $p$-adic digits beyond the Hodge polygon in both pieces (my estimate from the Newton-identity bounds). The cost grows like the fifth power of the number of digits and is out of reach on the 15 GB machine I used. Available now: the slope-1 polynomials modulo $p$ of both pieces at the twelve primes, and the full Frobenius matrices modulo $p^3$ at $p=19$ and $31$.

**Reproduction.** A patch against `ToricControlledReduction`, a driver, the analysis script and the output data (not linked here, in line with the discussion link policy; available as an attachment on request). Initialisation takes about a minute per piece and prime, the Frobenius columns seconds.

Credit: Edgar Costa, David Harvey and Kiran Kedlaya for the method and Costa for the software; `Robertboy18` for the question and the reduction of degree 6 to simplicity; `kmehltretter82` and `benediamond` for the core reduction on this thread; the repository authors' Chapters 2 and 3B. Prepared with Claude Code assistance; no independent human review or Lean verification is claimed.

---
_Generated by [Claude Code](https://claude.ai/code)_
