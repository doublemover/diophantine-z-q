# One exact Γ descent branch from a norm certificate, without factoring θ

This is a follow-on to the [oriented \(\sqrt5\) descent](../ct-original-scalar-gamma-relative-sqrt5-r1/GAMMA-ORIENTED-SQRT5-DESCENT.md), retaining the same actual scalar coefficient \(\delta\). It accepts a rational factorization \(\delta=N_{K/\mathbf Q}(\zeta)\) for \(K=\mathbf Q(\sqrt5)\), not a declaration that the factorization exists. The missing \(\sqrt5\)-norm, the remaining genus-one intersection point, and any alternative hidden orientations remain distinct.

## 1. No squarefree factorization is needed for one branch

Given \(\zeta\) with this exact norm, arrange that it is totally positive (its norm is positive). Write it in \(1,\omega\) and clear rational denominators. Divide the two integer coefficients by their positive gcd to get a primitive, totally positive \(\alpha\in R=\mathbf Z[\omega]\). Then
\[
              N(\alpha)=\delta k^2,\qquad k\in\mathbf Q^\times .
\]
The ideals of \(\alpha,\overline\alpha\) are coprime. At a split or inert prime this follows from integer content; at the only ramified prime, 5, primitive content bounds the order by 1 whereas \(v_5(N\alpha)\) is even, so it is zero. In particular, every known odd-depth prime \(p\mid\theta\) has one orientation read off from the two reductions of \(\alpha\), with odd order on its selected arm. Unseen factors of \(N(\alpha)\) need never be computed for the subsequent single-branch problem. Square factors of \(N\alpha\) are harmless: in the PID \(R\), the ideal factorization class of \(\alpha\) modulo square depends just on its odd supported arms, and the remaining totally positive unit is a square.

At \(p_*=16782959\), test the exact forced-orientation row of the previous note using the opposite reduction of \(\alpha\). If it fails, let \(\pi_*\) be the generator for the currently selected prime and replace \(\alpha\) by
\[
     \alpha'=\alpha(\overline\pi_*/\pi_*)^{v_{\pi_*}(\alpha)} .
\]
The exponent is found by successive exact division by the one already known generator. This preserves norm, total positivity and primitivity. It flips exactly the odd arm at \(p_*\), and the parameter-independent row calculation proves that it passes. Now read the five \(\beta\) residue requirements and first three visible \(\theta\) requirements on this same \(\alpha'\); their eight masks have rank 8 and determine \(g,e=\beta/g\) uniquely.

It remains to find a rational point on the two quadrics with \(\alpha'\) from (3) of the preceding note, equivalently
\[
            gX^2-e(2+\sqrt5)^2N^2=\alpha' z^2,\quad
            X,N\in\mathbf Q,\ z\in K .
\]
A nonzero rational solution needs neither coprime verification nor a squarefree norm for soundness: taking norms gives
\[
 F\!\left(\frac{N}{gX}\right)
    =\delta\left(\frac{k N_{K/\mathbf Q}(z)}{gX^2}\right)^2 .
\]
The exceptional case \(X=0\) is excluded by total positivity, and \(N=0\) by nonsquare \(\delta\), so the displayed raw inverse is valid. Conversely, a rational point of Γ induces *some* norm branch of this form: choose a primitive chart with the positive factor \(A\) of the preceding note, and rescale \(A\) by a rational factor so that its norm is exactly \(\delta\). Primitive content then recovers \(A\), its orientation already passes, and the unique sourced \(g\) is the given partition. Arbitrarily choosing a norm certificate could select a branch having no rational point. This is not a local-global theorem.

## 2. All orientation residue tests are jointly linear when true factors are supplied

If a complete split \(\theta=p_1\cdots p_n\) is supplied, choose one baseline prime generator \(\pi_i\) for each \(p_i\) and let \(x_i\) select its conjugate. At a \(\beta\)-place the coefficient of \(x_i\) in the sampled residue bit is \([(\tfrac{p_i}{p})=-1]\) (zero at ramified 5). At a \(p_i\)-place the off-diagonal coefficient of \(x_j\), \(j\ne i\), in the opposite residue bit is also \([(\tfrac{p_j}{p_i})=-1]\): changing generator multiplies that unit squareclass by its rational norm. Switching the tested place itself changes the combined contributions of all \(j\ne i\) by \([(\tfrac{\theta/p_i}{p_i})=-1]\), **independent** of their other orientation bits. The contribution of \(\pi_i\) at its opposite place is unchanged; the right-hand factor \(8\sqrt5\) changes by \(-1\). Thus the diagonal coefficient in the equation is \([(\tfrac{-\theta/p_i}{p_i})=-1]\). The orientation and partition residue screen is one ordinary binary linear system, not an exponential enumeration, although there can be multiple resulting genus-one intersections.

No literal norm certificate or actual rational point was obtained. The independent small replay exercises exact content, reflection, and all sixteen orientation identities on the visible-only product **as an algebraic control**; that product is not the original squareclass. The literal \(p_*\) stripped squareclass and all nine partition masks remain the exact original ones.
