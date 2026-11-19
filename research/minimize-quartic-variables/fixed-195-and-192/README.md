# Fixed-N three-detector quartics: 195 and 192 rational coordinates, input included
These two explicit single polynomials project onto Z under the listed supplier premises of José Brox v62 with the **fixed numeric parameter N=15**. See PROOF195.md for the complete argument and original v62 manuscript for the exact retained arithmetic assumptions. This is distinct from the earlier six-unit 192-coordinate *family* with an unknown sufficient N. No unconditional Hilbert-tenth or least-variable claim.

|total (witnesses)|quadrics|expanded monomials|ASCII bytes|coefficient bits|
|---|---:|---:|---:|---:|
|195 (194)|172|2,909|67,773|217|
|192 (191)|169|2,914|69,909|269|

**The three additional cuts.** In each contact chart of the 195 proof write f=Tj−3/22, w=1/f, y=w², and P(y)=Σ cᵢ yⁱ=∏(1−(3/22−θ)²y) with c₅≠0. Define a=c₄/(2c₅), b=(c₃/c₅−a²)/2. Replace both the old y² storage and the old middle-polynomial coordinate by the single v given by f v=y²+a y+b. It is unique because the unchanged w guard forces f≠0. The quadratic
  R=c₅v²+(c₂−2c₅ab)y²+(c₁−c₅b²)y+c₀
is exactly P(y): v²=y(y²+ay+b)². The new v is forced from any old witness; conversely both old intermediates are uniquely restored from y. This gives an isomorphism of the two decoded rational witness sets, fixing x1, unlike the earlier 229→195 arithmetic transfer. All three pole arguments and effective inequalities are unchanged. This interpolation was proposed in the independent arithmetic research lane, before a second reviewer independently verified the two decoded maps and actual expanded literal.

**Verify.** Run `python -B verify.py 195` and `python -B verify.py 192` from any directory, Python 3.9+ standard library. The checker reads pinned published tables, verifies each physical residual and the proper unit guard after all weight and coefficient rescalings, checks the count, primitive normalization and input, independently expands each literal, and reproduces the exact bytes. The tables use sorted pairs [coordinate-index-list, integer coefficient], with [] denoting the constant monomial. No solver, network, or additional inputs. SHA256SUMS.json records every payload besides itself. ATTRIBUTION.md and LICENSE cover the upstream CC-BY-4.0 attribution and adaptations. The checks do not reprove the deep supplier hypotheses.
