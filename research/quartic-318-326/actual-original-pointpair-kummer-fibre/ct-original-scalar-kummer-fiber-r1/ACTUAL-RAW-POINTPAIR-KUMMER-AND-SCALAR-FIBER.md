# The raw PointPair is an open Kummer surface; an exact scalar fibre is everywhere local

An independent global target for the same literal scalar, not the \(k=0\) torsor, not the selected \(n,n\theta\) ranks, and not a new rational point. Fix \(b\) with the numerical Ready conditions, \(\mu=b/17=\beta c^2\), \(\delta=1-\mu=\theta e^2>0\), \(\beta,\theta\) positive squarefree, \(c,e>0\). Here both classes are nonsquare on the original materialized scalar. Set \(B=17b=\beta\rho^2,\ \rho=17c>0\). Preserve the literal two [PointPair equations](../../joined-work-20261120/linear-q-original-forward-portable-r1/source-interface/NormalizedPolePoints318.lean), including the same \(B^2\delta\) in the second twist.

## 1. Exact conics and raw reverse map

For the old common parameter T and nonzero s, put \(z=T/B,\ z'=\delta z/(s/B)^2\). Dividing the ordinates respectively by \(\beta\rho^3,\ \beta\rho^3s^3\) gives two points on the **same** rational conic
\[
       y^2=\beta(1-z)(1+3z).
\]
Its parametrization with homogeneous coordinate \([a:b_0]\) is
\[
 z=(a^2-\beta b_0^2)/(a^2+3\beta b_0^2),\qquad
 y=-4\beta a b_0/(a^2+3\beta b_0^2).
\]
This follows by the line \(y=t(z-1)\) through \((1,0)\), \(t=a/b_0\); the remaining point at \(z=1\) is \(t=\infty\). The denominator is nonzero over \(\mathbb Q\) by \(\beta>0\). Neither numerator of z can vanish rationally since \(\beta\) is nonsquare. Write \(f_\beta(a,b_0)=(a^2-\beta b_0^2)(a^2+3\beta b_0^2)\). Then the exact remaining compatibility is
\[
       W^2=\delta f_\beta(a,b_0)f_\beta(a',b'_0)
\]
on the double cover of \(\mathbb P^1\times\mathbb P^1\), with W of bidegree \((2,2)\). In the reverse direction put
\[
 q=\frac{W}{(a^2+3\beta b_0^2)((a')^2-\beta (b'_0)^2)},\qquad
        T=Bz,\quad s=Bq,\quad y_1=\beta\rho^3 y,\quad y_2=\beta\rho^3s^3 y'.
\]
At any such rational point the denominators and q are nonzero. The double-cover relation says \(q^2=\delta z/z'\), so substitution gives the **actual** two equations, with the same s and T and no chosen elliptic rank. Conversely an actual PointPair gives this conic pair and W by the same formula. Homogeneous formulas allow either conic parameter to be infinity without division by its zero second homogeneous coordinate.

Since \(\delta\) is nonsquare, a rational pair cannot have \(z=z'\), so it cannot have \(t'=t\) or \(t'=-t\) (in rational projective parameters). Infinities or zeros of an individual t are **not** excluded from the original PointPair: they give respectively z=1 or z=-1/3 and hence one zero ordinate. Two infinities or two zeros would force \(\delta\) square; infinity paired with zero would give \(q^2<0\). The original interface only requires \(s\ne0\). To obtain both nonzero ordinates, require both parameters finite and nonzero.

## 2. Exact Kummer geometry, and why existing generic theorems do not apply

The two factors are the smooth projective quartics
\[
 C_1:v^2=f_\beta(t,1),\qquad C_\delta:(v')^2=\delta f_\beta(t',1),
\]
with simultaneous sign involution. Their product quotient has invariant W=\(vv'\) and the displayed double-cover model. Over the algebraic closure the two involutions have four fixed points each; the resolution is the Kummer surface of this product of 2-coverings.

On \(C_1\) the birational map to the literal 2-isogenous model is
\[
 X=2(v+t^2+\beta),\qquad Y=2Xt,\qquad
 E'_\beta:Y^2=X(X^2-4\beta X+16\beta^2).
\]
Indeed \((v-(t^2+\beta))(v+(t^2+\beta))=-4\beta^2\), so \(t^2=X/4-\beta+4\beta^2/X\). The infinity with \(v\sim t^2+\beta\) gives O and the other gives \(T_0=(0,0)\). The involution \(v\mapsto-v\) acts by \(X\mapsto16\beta^2/X,\ Y\mapsto16\beta^2Y/X^2\), exactly \(T_0-P\), **not** negation for this origin. Choose a half R of \(T_0\) geometrically. In coordinates \(P-R\) the involution is negation, and the \(C_1\) 2-covering is \(P\mapsto[2]P-T_0\), with class \(\sigma R-R\in E'_\beta[2]\). Twisting by \(\delta\) changes the linear Galois action by sign, but not this translation cocycle (its values have order two). Thus \(C_\delta\) has Jacobian \(E'_{\beta\delta}\), Q-isomorphic to \(E'_{\beta\theta}\), and the same 2-covering cocycle under the common 2-torsion identification. No rational half R is asserted.

Both Jacobians have 2-division field \(\mathbb Q(\sqrt{-3})\), not full rational 2-torsion. Both branch quartics have common biquadratic splitting field \(\mathbb Q(\sqrt\beta,\sqrt{-3\beta})\), with independent real and imaginary root classes. They are not \(S_4\) quartics and their discriminant valuation parities agree under a scalar twist (multiplication by \(\delta\) multiplies quartic discriminant by \(\delta^6\)). Thus [Harpaz–Skorobogatov 2016, Theorem A](https://msp.org/ant/2016/10-4/ant-v10-n4-s.pdf) does not apply; neither does the full-rational-2/disjoint multiplicative-places result summarized in [Harpaz 2019, Introduction equations (1)–(2)](https://www.math.univ-paris13.fr/~harpaz/Kummer_second_descent.pdf). In fact \(j(E'_\beta)=2048/3\), so potential multiplicative reduction can only occur above 3, where the original \(\delta\) is square and the two models are locally isomorphic. Their j is not an algebraic integer, hence there is no CM. For nonsquare \(\delta\), the geometric Hom space between these two twists is \(\mathbb Z\) with nontrivial quadratic sign action, so there is no nonzero rational isogeny between them; the standard graph of a rational isogeny also does not supply a section. This does not compute a Brauer–Manin obstruction, nor preclude a different theorem or actual rational point on this specific surface.

## 3. One exact everywhere-local fibre independent of k=0

Set **the fixed second parameter** \(t'=1/c\), using the unchanged numerical scalar \(c\ne0\), and \(\lambda=1+3\mu>0\). Then
\[
 f_\beta(1/c,1)=\delta\,\lambda/c^4,\qquad
           V^2=\lambda f_\beta(t,1)
\]
is the precise resulting fibre, with \(V=c^2 W/\delta\). If it has a rational point, the explicit maps of §1 recover the original PointPair. For the materialized scalar \(\lambda\) is nonsquare, verified below, so the two points at infinity of this quartic do not give rational points. The point \(t=0\) has negative right side; \(t=\pm1/c\) has right side of nonsquare class \(\delta\); and \(f_\beta(t,1)\) has no rational zero. Thus an actual rational point of this fibre has finite nonzero t and \(t\ne\pm t'\); it generates **two nonzero ordinates**. If \(\lambda\) were square, either infinity here would itself give a valid original PointPair with first ordinate zero, via §1, not evidence of a nontorsion point.

The fibre is everywhere locally soluble, with points off any specified finite exceptional t-set. At 2 and 3, \(\lambda=1+3\mu\) is square by the old positive depths; at \(p\mid\beta,\ p\ge5\) it is a square unit since \(\mu\) has positive depth. At these places one can start at a smooth infinity and perturb. At any other \(p\ge5\) where \(v_p(\lambda)\) is even, pass to a unit quadratic twist of the smooth separable quartic (the only possible bad primes of \(f_\beta\) are \(2,3,\beta\)). The projective genus-one reduction has an \(\mathbb F_p\)-point by the Hasse bound, which lifts. Negative \(v_p(\lambda)\) is always even because then \(v_p(\mu)<0\) is even. At a remaining odd depth, \(\mu\) is a unit and \(\lambda\equiv0\) gives \(-3\beta c^2\equiv1\bmod p\). Thus \(t^2=-3\beta\) has a simple local root on \(f_\beta\), giving a smooth point which may be perturbed off the branch. At infinity in the archimedean sense, take a sufficiently large real t. All these genus-one local points can be perturbed to nonzero V and regular finite t avoiding \(0,\pm t'\), preserving the chosen second parameter. Consequently the raw surface is everywhere locally soluble in its actual useful open, not merely at boundary cycles.

There is an exact elliptic restatement: by \(x=\lambda t^2,\ y=\lambda t V\), a rational affine point gives an actual point of \(E_{\beta\lambda}:y^2=x(x-\beta\lambda)(x+3\beta\lambda)\) with the **single first x-class \(\lambda\)**. Conversely any rational point with that literal nonzero x-class recovers \(t,V\) by taking \(t^2=x/\lambda\). The other retained mark and the originally selected twist pair are not assumed. The fixed fibre has no generic section over \(\mathbb Q(c)\): its trivialization after adjoining \(\sqrt{1+3\beta c^2}\) is over a rational conic (point at c=0). A map from that genus-zero function field to the fixed smooth projective genus-one quartic \(v^2=f_\beta(t,1)\) is constant. Constant t would give a rational branch root or a rational infinity of the nonsquare generic twist, neither available. Equivalently the constant point would have to be fixed by inversion of v under the nontrivial automorphism, and its rational parameter would then be a branch root. This blocks universal formulas over that generic parameter, not actual arithmetic specialization.

## 4. The literal original scalar: compact checks only

Use the exact admitted original scalar \(a=0,\ h=473592745039516333133760\) and frozen J. Its \(\beta=204618888056724185\) and \(c=12W_{\rm src}/(1+A_{\rm src})\), with \(A_{\rm src}=114444R_{\rm input}\) and W the untouched elliptic-chart circuit. At two actual denominator primes \(181,1346909\), the normalizer has depth one and the exact source \(W_{\rm src}\) is a unit (residues 146 and 429536). The standalone replay verifies these using the given annihilators on the actual \(\mathbb F_{p^2}\) curves before shortening indices. Therefore \(v_p(\lambda)=-2\) at both, and its stripped unit has class \(3\beta\) because \(p^2\lambda\equiv3\beta(12W_{\rm src}/((1+A_{\rm src})/p))^2\bmod p\). Both are nonsquares. This rules out the rational infinity shortcut, not a point at finite t. The fibre remains a distinct everywhere-local arithmetic target. No new source parameter, analytic rank, Brauer–Manin point or rational PointPair was produced.

Replay: python3 -B verify_actual_scalar_lambda.py | cmp - EXACT-ACTUAL-SCALAR-LAMBDA.json. No Lean build or remote write.
