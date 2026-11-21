# Exact local solvability criterion for the literal PointPair equations

This concerns the two equations in **NormalizedPolePoints318.PointPair**, not a separately chosen normalized genus-one marked cover or an all-place rational approximation. No Lean run is claimed.

**Theorem.** Let \(b\ne0,17\) in \(\mathbb Q_p\), with \(p\ge5,\ p\ne17\). The literal PointPair has a \(\mathbb Q_p\)-solution if and only if \(v_p(b)\) is not a negative odd integer. Whenever it has a solution, there is one with nonzero second multiplier, parameter, and both ordinates. Consequently, for \(b\in\mathbb Q\) positive, \(b\ne17\), with
\[
v_2(b)\ge3,\qquad v_3(b)\ge1,\qquad v_{17}(b)\ge2,
\]
the existence of local PointPairs at every place, including with nonzero ordinates, is equivalent to the reduced rational denominator of \(b\) being a square. This theorem does not require \(b\) itself to be a local square; that is a separate existing small-place CRT requirement.

## Literal variables and the obstruction

Put \(B=17b\) and \(V=B^2(1-b/17)\). In the source, for the same parameter \(P\) and multiplier \(s\ne0\), the two square equations are
\[
y_1^2=B(B-P)(B+3P),\qquad
y_2^2=(Bs^2)(Bs^2-PV)(Bs^2+3PV).
\]
Writing \(t=P/B,\ X=y_1/B,\ Z=y_2/(Bs)\), these are **equivalently**
\[
 X^2=B(1-t)(1+3t),\qquad
 Z^2=B(s^2-tV)(s^2+3tV).
\]
The inverse substitution is \(P=Bt,\ y_1=BX,\ y_2=BsZ\). No elliptic curve, coefficient, or parameter has been reselected.

For \(p\ge5,\ p\ne17\), suppose \(k=v_p(b)<0\) is odd. Then \(v_p(B)=k,\ v_p(V)=3k\). If \(v_p(t)<0\), the two factors in the first equation both have valuation \(v_p(t)\) (3 is a unit); if \(v_p(t)>0\) or \(t=0\), they are both units. Either alternative gives a nonzero nonsquare RHS, so any solution, including a torsion first ordinate, has \(v_p(t)=0\). Now \(v_p(tV)=3k\) is odd but \(v_p(s^2)\) is even. In the second equation the two factors therefore share the same strict-minimum valuation, are nonzero, and their product has even valuation. The extra \(B\) makes the RHS odd, a contradiction. This proves necessity even when zero ordinates are allowed.

## Sufficiency at odd good primes, including negative even depth

Two easy cases also apply at the small primes when their stated square criterion holds.

* If \(B\) is a square, start with \(t=0,\ s=1\), where both displayed RHS are the same nonzero square \(B\). A sufficiently small nonzero \(t\) keeps both in the open square class.
* If \(V\) is a square, set \(s=\sqrt V\) and take \(t\) near 1 with \(X^2=B(1-t)(1+3t)\) small and nonzero. Such \(t\) exist: the displayed RHS has simple zero at \(t=1\) with derivative \(-4B\ne0\), so it takes every sufficiently small local square by the local inverse function theorem. Then \(Z=VX\) and, in the literal variables, \(y_2=s^3y_1\).

Suppose now \(B,V\) are both nonsquares and \(p\ge5,\ p\ne17\). Positive \(v_p(b)\) would imply \(1-b/17\in1+p\mathbb Z_p\), hence \(V\) square. If \(v_p(b)=0\) then \(B\) is a unit; \(v_p(1-b/17)>0\) would force \(B\equiv17^2\bmod p\), hence \(B\) square. Thus both \(B,V\) are units in the remaining zero-depth case. If \(v_p(b)<0\) is even, then \(v_p(B)=v_p(b)\) and \(v_p(V)=3v_p(b)\) are both even. In either case put
\[
 B=u\beta^2,\quad V=v\gamma^2,\quad
 \beta=p^{v_p(B)/2},\quad \gamma=p^{v_p(V)/2},\quad
 u,v\in\mathbb Z_p^\times.
\]
These operations may divide the old coordinates by large \(p\) powers; they do not require the original coordinates to be integral. Put \(s=\gamma z\), \(Z=\beta\gamma^2Y\). At \(t=1\), the literal second equation becomes
\[
  Y^2=u(z^2-v)(z^2+3v),
  \qquad y_2=B\beta\gamma^3 zY .
\]
We construct a point with \(zY\ne0\).

* For \(p\ge11\), the reduction has four simple distinct geometric branch roots and its smooth geometrically integral projective completion has genus one. The [Hasse–Weil bound](https://doi.org/10.1090/S0002-9904-1949-09219-4) gives more than four rational points since \(p+1-2\sqrt p>4\). At most two lie above \(z=0\) and at most two at infinity. So there is a finite point with \(z\ne0\). Lift by the smooth equation; if the point is a branch point with \(Y=0\), the derivative in \(z\) is a unit, so one may prescribe a sufficiently small nonzero \(Y\) and still lift with \(z\) a unit.
* At \(5\), the unit \(v\) is a nonsquare and \(-3\) is a nonsquare. The simple branch \(z^2=-3v\) has nonzero \(z\); lift and perturb \(Y\) as above. At \(7\), \(z^2=3v\) is a nonzero square since both \(3\) and \(v\) are nonsquares. The RHS then equals \(12uv^2\bmod7\), a nonzero square since \(12\equiv5\) and \(u\) are nonsquares. The solution lifts immediately. These are both actual unit-phase checks and do not assume an origin on the special quartic.

The resulting second ordinate is nonzero at \(t=1\) and \(s\ne0\). Fix that same \(s\). The second RHS stays a nonzero square for all sufficiently nearby \(t\). Simultaneously select \(t\) in that neighborhood using the same first local inverse-function argument at \(t=1\), with \(X\ne0\). This gives the exact literal pair with a single \(P=Bt\), and both ordinates nonzero. This also proves the stated nondegeneracy equivalence.

## Small places, real place, and actual meaning

Under the three displayed small-place depths, \(1-b/17\) is a square: it is in \(1+8\mathbb Z_2\), \(1+3\mathbb Z_3\), or \(1+17\mathbb Z_{17}\) respectively. Thus \(V\) is a nonzero square and the easy local case applies. At the real place \(B>0\) is a square, also an easy case. At every other place the obstruction is exactly negative odd \(v_p(b)\), equivalent over the rationals to the reduced denominator failing to be a square. This proves the global-to-local equivalence claimed; it is **not** a Hasse principle over \(\mathbb Q\).

For a retained good mover such as \(p_a=415721\) on the repaired same-scale candidate, depth \(+1\) of the literal pole is permitted and even gives the easy \(V\)-square case. A negative odd depth in a merged other contact can instead be a genuine local failure. To apply the theorem to the final construction one must still exhibit a single rational parameter \(w\) producing the right original poles, square reduced denominators, and all other guards, and then exhibit rational pairs on these surfaces (or supply the actual global rank and realization argument). No assertion about such a global point follows from these local checks.

Signed: independent reviewer / author of this local proof, 2026-11-21 UTC.
