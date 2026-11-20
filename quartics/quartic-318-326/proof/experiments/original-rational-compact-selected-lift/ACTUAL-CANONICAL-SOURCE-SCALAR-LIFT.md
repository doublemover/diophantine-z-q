# Canonical scalar lift of the entire original compact comparison

Let \(j:X\to\mathbf P^1_R\) be the original compact j-map and let
\(R\to S\) be the chosen coefficient field map. The source is literally
\[
 X_S=\operatorname{pullback}
  \bigl(X\xrightarrow{j}\mathbf P^1_R\to\operatorname{Spec}R,\;
     \operatorname{Spec}S\to\operatorname{Spec}R\bigr).
\]
No input claiming a model is this source is needed. Its modular
map is the unique lift through the proved original projective
pullback; the resulting square over \(j\) is an actual pullback.
An isomorphism over the old \(j\)-line transports to an isomorphism
of the entire scalar extensions over the new \(j\)-line. Equality of
those new maps is proved by their two actual projections, not
given as a supplementary contract.

Apply this to the exact earlier relative-normalization construction:
the same entire rational ordinary chart gives the normalization
over the actual projective \(\mathbb Q\)-line and an over-\(j\)
comparison to the stated genuine compact curve. Both curves are
then canonically pulled to the one selected field \(L\). The
new source is neither a chosen component nor a new evaluation
field presented independently of the old surface. There is no
bound on \([L:\mathbb Q]\) in this construction. In particular an
auxiliary field used to evaluate the \(j=1\) Hodge minor is not
being used as an isogeny/GR field.

## Weakest remaining connectedness seam for the degree argument

Full compact analytic comparison is not needed to get one whole
generic field. It suffices that the *entire genuine ordinary open*
of the same algebraic scalar extension analytifies to
\[
 \Gamma_1(M)\backslash
 \bigl(\mathfrak H\setminus
    (\mathrm{SL}_2(\mathbb Z)i\cup\mathrm{SL}_2(\mathbb Z)\rho)\bigr).
\]
The two removed orbits are countable, and the punctured upper
half-plane is path-connected. For example, for two surviving
points take an intermediate point on a short line in the half-plane
transverse to the two original endpoints. For each puncture, at most
one intermediate point makes one segment hit that puncture, after
choosing the line avoiding the original endpoints; exclude the
countable union. Convexity keeps the two segments in the upper
half-plane. Its quotient is connected. The upper-half-plane
description of the moduli quotient is [Snowden, Lecture 12](https://websites.umich.edu/~asnowden/teaching/2013/679/L12.html).

If the compact algebraic curve is smooth, the complex scalar
extension is regular and all components are one-dimensional.
Every component meets the entire ordinary open: otherwise that
component would be in the finite inverse image of
\(\{0,1728,\infty\}\) under the same finite \(j\)-map, contradicting
its positive dimension. Thus the open is dense in the whole
compact curve. A separation of the algebraic compact would
separate its ordinary open, whose complex analytification is
connected. This yields algebraic connectedness; regular
Noetherian components are disjoint open, hence the curve is
integral. In the characteristic-zero curve setting the
genuine normal one-dimensional compact model is smooth over
the perfect field, so smoothness need not require a stable
integral model. The full generic fiber of the actual changed
compact j-map is \(\operatorname{Spec}\mathbb C(X_\mathbb C)\)
by finite localization over \(\mathbb C(j)\).

A small possible native topology lemma uses
Mathlib/Analysis/Normed/Module/Connected.lean
(blob 4f4d4005...), Set.Countable.isPathConnected_compl_of_one_lt_rank,
after the explicit homeomorphism of the half-plane with
\(\mathbb C\), \(x+iy\mapsto x+i\log y\).
The inverse \(x+it\mapsto x+i\exp t\) avoids any need for a compact
surface or a properness theorem. First identify the genuine
ordinary analytic moduli open, not just an abstract connected
quotient; the native scheme/analytic comparison is still absent.
See [Stacks 0361](https://stacks.math.columbia.edu/tag/0361) and
[Stacks 0366](https://stacks.math.columbia.edu/tag/0366) for the
actual geometry after extension.

Scope: source-only canonical constant scalar lift and exact whole
curve over-\(j\) comparison. This paper reduction does not claim
the genuine ordinary analytic classification or geometric
integrality was constructed in Lean.
