**The accepted moving-conic construction extends, with only its two target-specific steps changed, to all ten remaining basic $q=1$ holdout targets.** Prepared with Claude Code assistance on behalf of `DiamondJM`; I read the whole thread and the accepted [solution write-up](https://github.com/hodge-computer/sextics/blob/main/data/holdout/solution.md) of PR #128 first. The protected data of every instance below are unchanged at upstream `bfb13916d06dbf9bfe9034222f6999f5c705744a`. **No Lean `HasCertificate` proof or solve PR is claimed yet; this is a mathematical observation with exact symbolic checks, and the Lean adaptation is being compiled.**

**Why the construction is target-independent.** In `fqlx`'s proof (Sections 4–6, 8–10 of the write-up, and `conic_target_residue_solution` in the Lean sources) the moving conic solves the residue equation for *every* polynomial source $B\in K_b[X_0,X_1,X_2,S,P]$ on the quotient $H$, and clearing, trace and homogeneous extraction never look at $A$. Only Section 2 (the quotient source $B$ obtained from $A$) and Section 7 (the deck trace that removes the reflected companion) depend on the target.

**The two target-specific steps for a monomial.** Write $A=X^{a}Y_0^{b_0}Y_1^{b_1}Y_2^{b_2}$ and pull back along $(Y_0,Y_1,Y_2)=(\alpha T,y,\beta T)$. Symmetrising the density $A\cdot(-T/\alpha^5)$ under $y\leftrightarrow T$ and dividing by $2(y^2-T^2)$ gives, with $k=b_0+b_2+1-b_1$,

$$J_c\,B=A-A\,(y/T)^{k},\qquad J_c=\frac{2\alpha^5(T^2-y^2)}{T},$$

and $B$ is a polynomial of weighted degree five in $(X_0,X_1,X_2,S,P)$ exactly when $k$ is even, which holds for every $Y$-odd target. The companion $A(y/T)^k$ is a $\zeta^{-k}$-eigenvector of the deck automorphism $T\mapsto\zeta T$ fixing the physical field, so its normalized trace vanishes whenever $6\nmid k$; a primitive cube root serves every $k\in\{\pm2,4\}$. For the accepted target $k=4$. For the ten open targets:

| instance | $A$ | $k$ | quotient source $B$ |
|---|---|---|---|
| `holdout-x13-y13` | $X_1^3Y_1^3$ | $-2$ | $-X_1^3P/(2\alpha^5)$ |
| `holdout-p3` | $X_2^3Y_2^3$ | $4$ | $\beta^3X_2^3S/(2\alpha^5)$ |
| `holdout-x12-p-y02` | $X_1^2X_2Y_0^2Y_2$ | $4$ | $\beta X_1^2X_2S/(2\alpha^3)$ |
| `holdout-p-y14` | $X_2Y_1^4Y_2$ | $-2$ | $-\beta X_2P^2/(2\alpha^5)$ |
| `holdout-x1-y04-y1` | $X_1Y_0^4Y_1$ | $4$ | $X_1SP/(2\alpha)$ |
| `holdout-x0-y03-y12` | $X_0Y_0^3Y_1^2$ | $2$ | $X_0P^2/(2\alpha^2)$ |
| `holdout-all-six` | $X_0X_1X_2Y_0Y_1Y_2$ | $2$ | $\beta X_0X_1X_2P/(2\alpha^4)$ |
| `holdout-x0-x14-y0` | $X_0X_1^4Y_0$ | $2$ | $X_0X_1^4/(2\alpha^4)$ |
| `holdout-x04-p` | $X_0^4X_2Y_2$ | $2$ | $\beta X_0^4X_2/(2\alpha^5)$ |

For $k<0$ the companion $A(y/T)^k=(A/Y_1^{|k|})\,T^{|k|}$ is a physical polynomial times $T^{|k|}$, so the trace argument needs $\operatorname{tr}(T^{2})=0$ instead of $\operatorname{tr}(T^{-4})=0$; the same eigenvector lemma gives it. Every identity $J_cB=A-A(y/T)^k$ and its $\partial_{X_0}$-companion for the normal source were verified exactly with sympy, independently of the Lean sources. This agrees with the ten-dimensional count of `fringewidth` and the maintainers: the construction serves both conjugate character pieces (six targets with $k\in\{4,-2\}$ and four with $k=2$).

**Boundary.** The second summand of `holdout-bundle`, $X_0^3Y_0Y_1^2$, has $k=0$: its reflected companion equals $A$ itself, the symmetrised source $B$ is zero, and this cover gives nothing, which matches the separate finite-quotient support recorded in its motivation. Monomial targets with $b_1-b_0-b_2\equiv1\pmod 6$ are outside this route for the same reason.

**Status.** For each of the nine open monomial targets the accepted Lean sources need changes in six modules only (the source and companion polynomials, two scalar identities, the trace lemma for $T^{\mp2}$, and the binding of the companion in the certificate closure); the fifty-odd remaining modules are reused verbatim with `fqlx`'s attribution retained. The adapted modules are being compiled through CI; solution PRs will follow only after a clean compile and kernel replay. If `fqlx` or anyone else is already preparing these follow-ups, this comment is meant to help rather than compete: the table above is the complete target-specific input.

Credit: the entire construction is `fqlx`'s (PR #128), building on the repository's certificate framework by Benjamin E. Diamond and the earlier holdout work of `fringewidth`, `rbajaj5`, and `HeadOfNaps`; the only contribution here is the observation that it is source-agnostic and the explicit per-target data.
