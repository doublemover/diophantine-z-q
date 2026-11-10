# Explicit collected-coefficient heights and degree bounds for the original reduced polynomials

All328 predecessor sources remain byte-identical. Four new sources construct coefficient-growth bounds for the SAME original reduced polynomials; no generic geometric-sieve height assumption is accepted.

OriginalPolynomialExpansionBounds318 defines an explicit finite monomial expansion, retaining repeated exponents and actual rational coefficients before collection. Its weight is the sum of absolute real coefficient values. A triangle inequality proves every collected coefficient is bounded by this weight, including collisions/cancellation. Explicit disjoint-sum and product-index constructions give exact polynomial add/multiply and exact weight add/multiply identities. Constants and linear rows are constructed concretely.

OriginalReducedPolynomialExpansions318 builds actual finite expansions of the original firstP,secondP,productD and normK after the reduced substitution. It proves their exact polynomial identities and exact precollection masses, including the original factors2,t and exceptional secondP parameter t+2. This is symbolic equality in Q[X0,X1,X2], not equality on sample evaluations.

OriginalReducedCoefficientHeight318 proves the following budgets when each reduced linear row has mass<=H:
- firstP: |kappa|H^2+2|t|.
- secondP: |kappa(t+2)|H^2+2H^2.
- productD: (t^2+H^2)^2.
- normK: (|kappa|H^2+H^2+|t^2+2t|)^2+t^2(2H)^2.
It then derives actual row mass<=6lambda3 from the original Euclidean coordinate bounds, ordered shortest lengths, and |z|<=2lambda3. Hence every collected coefficient has a fully explicit budget at H=6lambda3. These are coefficient bounds, not merely source-box value bounds.

OriginalReducedDegreeBounds318 checks the actual substituted total degrees: firstP and secondP<=2; productD and normK<=4. It derives them from the linear-row degree bound using actual add/multiply/power inequalities, so zero or cancellation can only lower degree.

The quantitative geometric-sieve elimination/resultant and boundary/remainder estimates remain next; the full weighted Selberg remainder, optimized weights and simultaneous Gaussian prime production are not proved here. Four rational twist pairs and Anchor local-global remain separate.

Validation:8547 collected coefficients checked against the explicit budgets,840 degree checks and210 actual row-weight checks. All328 arithmetic/geometry checks rerun, including26198 residue inverses and352 content witnesses. Static332/222 closure only, no local Lean compilation.
