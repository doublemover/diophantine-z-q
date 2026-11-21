# The Gaussian lift norm can be forced on a same-squarepair representative

**One norm, not two.** Starting from any numerical Ready \(b\) with nonsquare \(\delta=1-b/17\), there are other Ready pole values with the **same ordered** squareclasses of \(\mu=b/17\) and \(\delta\), and with the Gaussian norm condition
\[
            (A'+3(D')^2)/3=r^2+s^2,\qquad r,s\in\mathbb Z
\]
for their reduced \(\mu'=A'/(D')^2\). They can approximate the original at all its old support primes and infinity. This does not enforce the primitive \(\sqrt3\)-norm of the same \(C'=(D')^2-A'\), does not alone give a full Selmer lift, and does not produce another literal original fold output.

## 1. Actual rational parameter with the same two classes

Write \(\mu=\beta c_0^2\), \(\delta=\theta e_0^2\) with \(\beta,\theta\) positive squarefree and \(c_0,e_0>0\). Both are nonsquare here (\(\beta\) includes 17, by Ready). On the same rational conic
\[
              \beta c^2+\theta e^2=1
\]
write \(u=1-\delta k^2,\ v=1+2\delta k+\delta k^2,\ w=1+2k+\delta k^2\). The exact parameter is
\[
           c=c_0 u/v,\qquad e=e_0 w/v .
\]
Indeed \(v^2-\delta w^2=\mu u^2\), by expansion, equivalently the quadratic norm of \((1+\sqrt\delta)(1+k\sqrt\delta)^2\). Its homogeneous quadratic coordinates \((c_0u,e_0w,v)\) have no common zero: for a finite k, \(v=w=0\) would give \(2k(\delta-1)=0\) and \(v=1\); at infinity \(v\) has nonzero coefficient \(\delta\). The map is nonconstant onto the smooth projective conic and has degree one because its pullback of a hyperplane has degree 2, the degree of the conic's hyperplane divisor. Thus it is a rational conic parametrization, not a multiple subcover. At \(k=0\) it recovers \(c_0,e_0\). No arbitrary square-class representative is changed in this computation.

Over this conic solve
\[
        x^2+y^2=1+\beta c^2/3 .
\]
After multiplying the two Gaussian coordinates by \(v\), this is the exact Châtelet equation
\[
        X^2+Y^2=F(k),\qquad F=v^2+(\mu/3)u^2 .
\]
Its leading coefficient is \(\delta^2(1+\mu/3)>0\). Its zeros do not coincide with \(v=0\) (the norm identity would force all three conic coordinates to vanish). On the conic the four zeros are exactly \(c^2=-3/\beta,\ e^2=4/\theta\). They are distinct; over the ground field they are a single orbit with root field
\[
                  K=\mathbb Q(\sqrt{-3\beta},\sqrt\theta).
\]
In fact \(F\) is irreducible **also over \(\mathbb Q(\mathrm i)\)**. The two squareclasses \(-3\beta,\theta\) are independent since \(\theta>0\) is nonsquare. The three quadratic subfields of K have classes \(-3\beta,\theta,-3\beta\theta\), none of class \(-1\): the positive class cannot be \(-1\) and both negative classes have odd valuation at 3. Here \(3\nmid\beta\theta\) by the Ready depth and \(\delta\equiv1\bmod3\); also \(17\mid\beta,\ 17\nmid\theta\), so 17 independently gives the same exclusion. Hence \(K\cap\mathbb Q(\mathrm i)=\mathbb Q\), so the orbit remains transitive over \(\mathbb Q(\mathrm i)\).

## 2. All places and weak approximation

Use [Colliot-Thélène–Sansuc–Swinnerton-Dyer, Intersections of two quadrics and Châtelet surfaces II, §8.11](https://geodesic.mathdoc.fr/item/JRAM_1987__374_152896/). The irreducible degree-four Châtelet case gives the Hasse principle and weak approximation on a smooth proper model of \(X^2-aY^2=F(k)\), \(a=-1\). This exact special-case implication is stated by [original coauthor Colliot-Thélène in his retrospective](https://api.repository.cam.ac.uk/server/api/core/bitstreams/7bbfcdef-68c3-4bb3-8a3f-a51453ec01a5/content), part 3 (the published version, Notices AMS vol. 66, p. 1064). We are not applying an unrestricted Hasse principle for two quadrics or for the genus-one marked cover.

Write \(g=1+\beta c^2/3\) on the conic. Its local norm condition is open whenever \(g\ne0\): at a split place there is no restriction, and at unramified inert odd places its valuation needs to be even. If a nominated conic point lies outside the birational coordinate chart, it has a nearby point in that chart with the same nonzero norm property. More explicitly:

- At infinity \(g>0\) on the entire real affine conic. At 2 and 3, use the old Ready point: \(g\) is a square unit by the actual depths \(v_2(\mu)\ge4,\ v_3(\mu)\ge2\).
- For \(p\ge5\) dividing \(\beta\), the old point has positive \(\mu\)-depth and \(g\) is a unit. Alternatively \(c=0,e=1/\sqrt\theta\) exists in \(\mathbb Q_p\) since the old \(\delta\) is a square unit there. For \(p\mid\theta\) the old point has \(\mu\equiv1\) and \(g\equiv4/3\) is a unit; alternatively take \(e=0,c=1/\sqrt\beta\). The supports of \(\beta,\theta\) are disjoint by the reduced Ready expression, and the same computations cover 17.
- At any old p≥5 with \(\mu\) or \(\delta\) of positive depth (even or odd), the displayed old point has \(g\) a unit, of residue 1 or \(4/3\). At a denominator prime of \(\mu\), \(v_p(g)=v_p(\mu)\) is even. Thus the old conic point is norm-compatible throughout \(2,3,\infty\) and at every prime in its actual reduced \(A,C,D\).
- At an odd split place for \(-1\) any nonzero \(g\) is a norm from the product algebra. At a remaining inert odd place \(p\ge7,\ p\nmid\beta\theta\), the projective conic modulo p is smooth and has \(p+1\) points. At most two are at infinity, and at most four have \(g=0\) on the affine chart (two possible \(c\)'s and two \(e\)'s). Since \(p+1>6\), there is a smooth affine residual point with unit \(g\); Hensel lifts the conic point and the unit is a Gaussian norm in the unramified quadratic extension. The smallest good p≥5 not in this count is 5, already split for \(-1\).

Thus the proper model has local points everywhere. Weak approximation supplies actual rational points in its common affine chart and arbitrarily deep prescribed **finite** old balls whose centres are norm-compatible; in particular all original \(A,C,D\)-support places together with 2,3 and an open real interval around \(c_0,e_0\) can be retained simultaneously. Extra finitely many places may be protected if their chosen local target has \(g\) a norm. An arbitrarily deep ball about a non-norm \(g\) cannot be protected, and is not claimed.

Set \(\mu'=\beta c^2,\ \delta'=\theta e^2\) from a rational point, choosing \(c,e\ne0\) and the same positive old real ranges. At each prime dividing \(\beta\), its positive old depth is retained. At other primes any negative depth of \(\mu'\) is even. Thus the reduced denominator of \(\mu'\) is a square, as is that of \(b'=17\mu'\) since the old 17-adic positive depth is retained. The 2,3,17 square/depth guards persist by openness of the local squareclass conditions. This is a genuine numerical Ready pole and preserves both ordered squareclasses exactly, not just finitely many tests.

Write \(\mu'=A'/(D')^2\) reduced. Then
\[
    (A'+3(D')^2)/3=(D'x)^2+(D'y)^2
\]
is a positive integer (by the retained 3-depth). A positive integer which is a rational Gaussian norm is an **integer** sum of two squares: all inert odd valuations are even by local norms, and Fermat's two-square criterion applies. Hence the claimed integer Gaussian lift norm holds. The construction can avoid the original rational base parameter by requiring a different real value in a sufficiently small open real ball on the projective conic, so it is not merely claiming that the original point already had a Gaussian norm.

## 3. Remaining same-class support condition

The [specified full-lift criterion](../ct-original-k0-first-character-r1/ACTUAL-K0-FIRST-CHARACTER-AND-EXACT-LIFT.md) additionally needs every prime of the **same** new \(C'\) to split \(\sqrt3\), equivalently a primitive integer representation \(u'^2-3v'^2=C'\). This condition can never hold if a prime of the fixed \(\theta\) is nonsplit. If all those primes split, avoiding new nonsplit primes in the square part of \(C'\) still means a simultaneous global support condition. The Gaussian Châtelet weak approximation statement does not enforce it by checking finite old balls. Substituting the earlier explicit degree-two conic parameter designed for primitive C raises the Gaussian polynomial to degree eight generically; the degree-four theorem above cannot be applied to that transformed polynomial without an independent reduction. No full lift, pairing sign, rational \(k=0\) point, or literal source-realization follows solely from the Gaussian norm.

No Lean build or remote write.
