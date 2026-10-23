Progress on **cycle-q2** along the cycle-three Jacobian route, prepared with Claude Code assistance on behalf of `DiamondJM`. This follows the note above. **No certificate, Lean proof, or solve PR is claimed.** Items marked *exact* are polynomial identities or exact rational linear algebra; *modular* means point counts mod small primes. The two caveats at the end are not yet closed.

**1. The q=2 target is a mixed second variation (exact).** $A=m_1m_2$ with $m_1=X_0X_1X_2Y_0Y_1Y_2$ and $m_2=X_0X_1X_2^2Y_0Y_1$, so
$$2A\,\Omega/F^3=\partial_{s_1}\partial_{s_2}\bigl(\Omega/F_s\bigr)\big|_{s=0},\qquad F_s=F+s_1m_1+s_2m_2 .$$
In the chart of `hodgepodgeconjecture`'s [cycle-three proof](https://github.com/hodge-computer/sextics/blob/main/data/cycle-three/solution.md) ($v=Y_0/X_0$, $c_1=(Y_1/X_1)/v$, $c_2=(Y_2/X_2)/v$), both directions add an $xyz$ term to the ternary cubic, with coefficients $g_1=v^3c_1c_2$ and $g_2=v^2c_1$.

**2. Jacobian invariants with an $xyz$ term.** For $U=ax^3+by^3+cz^3+dx^2y+ey^2z+fz^2x+m\,xyz$, the Hessian syzygy $H(H(U))=\lambda U+\mu H(U)$ gives, in cycle-three's normalization ($\eta^2=\xi^3+s_4\xi-s_6/4$):
$$48s_4=48(ae^2f+bdf^2+cd^2e)+216abc\,m-24def\,m-m^4,$$
$$216s_6=5832a^2b^2c^2+864a^2ce^3+864ab^2f^3+1296abcdef-540abc\,m^3-864abef^2m-864acde^2m+72ae^2fm^2$$
$$\qquad+864bc^2d^3-864bcd^2fm+72bdf^2m^2+72cd^2em^2-216d^2e^2f^2-36def\,m^3-m^6 .$$
These reduce to cycle-three's $s_4,s_6$ at $m=0$. *Modular check:* the cubic and the Weierstrass curve have equal point counts for 20 random cubics with $m\neq0$, mod 101, 103, 107 and 109. Cycle-three's model `a8`, `b256` also matches the physical cubics in 12 random fibres.

**3. Why cycle-three's model cannot carry the target (exact bookkeeping).** Write $A=s_4$, $B=-s_6/4$ for the Weierstrass coefficients. Their $s_1$-variations carry $v^3$, their $s_2$-variations carry $v^2$, $\partial_{s_1}\partial_{s_2}A=0$, and $\partial_{s_1}\partial_{s_2}B$ carries $v^5$ (all mod $v^6$). Gauss–Manin on the model,
$$\partial_{s_1}\partial_{s_2}\Bigl[\frac{d\xi}{\eta}\Bigr]=\Bigl[\frac{3(A_1\xi+B_1)(A_2\xi+B_2)}{4\eta^5}-\frac{A_{12}\xi+B_{12}}{2\eta^3}\Bigr]d\xi,$$
together with cycle-three's multiplier $-144Rv^3$, leaves a source carrying $v^2=T_3/R$. That is a function on the triple cover $T_3=Rv^2$ ($t=v^6=\tau^3$) but not on cycle-three's model. The $\zeta_6^2$ character in `why.md` is exactly this extra $v^2$.

**4. The triple-cover model.** Pulling cycle-three's Weierstrass family back along $(r:t)=(\rho^3:\tau^3)$ gives coefficients of degrees $(12,18)$ in $(\rho,\tau)$. They are minimal (orders $(6,0)$ at $\rho=0$ and $(3,0)$ at $\tau=0$), with nonconstant $j$. Over fixed $(c_1,c_2)$ the fibre is therefore an elliptic surface $S_3$ with $\chi=3$ and $p_g=2$. Cycle-three's fibres are rational elliptic surfaces ($p_g=0$), which is why every polynomial source has a primitive there. That theorem cannot hold on $S_3$.

**5. Hodge-level test (exact over $\mathbb Q$, at $(c_1,c_2)=(2,3),(3,5),(1,4)$).** View $S_3$ as $y^2=x^3+a(\rho,\tau)x+b(\rho,\tau)$ in $\mathbb P(1,1,6,9)$. The weighted Jacobian ring has $\dim R_1=2=p_g$, $\dim R_{37}=2=h^{0,2}$, socle $R_{38}$ of dimension 1, and $R_{39}=0$. In the target sector the Hodge numbers are $(1,10,1)$ (the invariant sector is $(0,8,0)$). The transported source is $\mathrm{Res}(P\Omega/G^3)+\mathrm{Res}(P'\Omega/G^2)$, where $P$ has weighted degree $33\le 37$, so it defines a class on the compact surface.
- $P\notin J_{37}$: fibrewise, the class has a nonzero transcendental $(0,2)$ part. No construction that only removes curves fibre by fibre can work. Consistently, the fibrewise Gauss–Manin equation has no rational solution with denominators $t^j\Delta^k$, $j\le4$, $k\le2$, numerator degree $\le40$.
- But $P\in J_{37}+\partial_{c_1}G\cdot S_{19}+\partial_{c_2}G\cdot S_{19}$: the Kodaira–Spencer images of the base directions span $R_{37}$. On the fourfold, the $(0,2)$ part can be absorbed by Gauss–Manin derivatives in $c_1,c_2$. There is no obstruction at this level.

In the target sector, Kodaira–Spencer maps $R_1\to R_{19}$ injectively (image of dimension 2) and $R_{19}$ onto $R_{37}$. So the transcendental sub-variation has Hodge numbers at least $(1,2,1)$.

**What is open.** Below the $(0,2)$ layer there is no pointwise test: on a two-dimensional base the derivatives of a correction can be prescribed freely at a point. The remaining question is global. Does $\Sigma$ vanish in the de Rham cohomology of the target-sector Gauss–Manin system (rank 12, transcendental part of rank $\ge4$) over $\mathbb C(c_1,c_2)$, modulo algebraic classes? That is a two-variable rational-integrability problem. If it has a solution, the primitive must vary with $(c_1,c_2)$: a $c$-direction analogue of cycle-three's first-variation identity, which cycle-three never needed. Caveats for an actual certificate: the multiplier $-144Rv^3$ should be re-derived with the $xyz$ term (it comes from a covariant identity valid for all ternary cubics), and the second-order moving-map correction must be written out.

**Reproduction.** https://github.com/DiamondJM/hodgeHoldout, branch `claude/inspiring-turing-tx2pbu`, directory `cycleq2/`: `model_check.py`, `triple_cover.py`, `invariants.py`, `inv_check.py`, `second_variation.py`, `gm.py`, `step2.py`, `solve_rational.py`, `jacobian_ring.py`, `ks_test.py`, `sectors.py`, with the derivation in `NOTES.md`.

Credit: `hodgepodgeconjecture`'s cycle-three construction, Jacobian model and chart, on which all of this builds; the classical invariant theory of ternary cubics, with the normalization following Tom Fisher as in that proof; Griffiths's residue theory and the Jacobian-ring description of weighted hypersurfaces; the repository authors' certificate formalism, with the certificate bridge attributed there to Benjamin E. Diamond. Prepared with Claude Code assistance; no independent human review or Lean verification is claimed.

---
_Generated by [Claude Code](https://claude.ai/code)_
