# Global finite-flat rank and exhaustive local branch orders

Status: uncompiled hosted-CI candidate. Structural validation and source review
are not kernel acceptance. No Lean ran locally.

The unchanged global projective j map is proved flat on both entire target
charts using its actual finite preimages, integral source/target and dominant
section maps over Dedekind polynomial charts. Its actual generic-stalk degree4
then gives rank4 at every scheme point, including all exceptional fibers.

The exact derivative of the original J function excludes every unlisted finite
branch parameter. All nonzero finite centered germs have order3 at -243, order2
at roots of D and order1 otherwise, including the simple point -27 above zero.
The finite-origin and reciprocal-origin cusp germs have orders3 and1. Every
actual projective complex scheme point is covered by a certificate containing
actual source/target charts, analytic germ, whole-neighborhood equality with the
scheme map and centered local order. The canonical q-disc orders remain tied
to the original full cusp-end type and compact analytic comparison.

These are exhaustive analytic local-order certificates, not yet a formal
scheme-theoretic ramification/divisor identity. General quotient/PEL family
inputs and the full318/326 arithmetic theorem remain separate. The original
rational arithmetic model and dense proper completion are inherited unchanged,
with no false integral extension through3.

## Exact application contract

1. Entire target chart coverage for flatness. Required: Flatness cannot be inferred from the Laurent open alone or by ignoring target infinity and elliptic fibers. Constructed: map_flat uses the actual original Fin2 target cover and restrict_chart_flat on every entire chart image. Application: Every target point is supplied by the original cover. The preimage is the actual full finite preimage, with no assumed replacement by a selected source chart.

2. Dedekind flatness hypotheses. Required: The section-flatness criterion requires integral source/target, actual dominance/finite map and Dedekind target section rings. Constructed: ProjectiveLineIntegral318 and ThreeJActualDominance318 supply actual integrality/dominance. ThreeJGlobalFinite318 supplies finiteness. Every original target chart is Spec Q[T], a Dedekind domain. Application: DedekindAffineFlat318 transports the exact chart section equivalence, obtains section-map injection from dominance and reduced target, then domain torsion-freeness and flatness. The morphism is unchanged throughout.

3. Actual rank at all target points. Required: Generic degree alone is not a rank theorem at ramified fibers. Constructed: rank_four applies FiniteFlatGenericRank318.finrank_eq_generic_degree to the same now finite-flat dominant integral map. Application: The actual generic pullback scalar action agrees with ThreeJActualGenericDegree318.pullbackAlgebra, whose degree4 was identified through the whole field square. Thus rank4 holds at every actual scheme point, including infinity and both exceptional values.

4. Ordinary derivative of the exact j function. Required: The listed exceptional orders must not omit unlisted finite ramification. Constructed: J_hasDerivAt differentiates the exact original J rational function and simplifies its derivative to (t+243)^2*D(t)/t^4. Application: At every nonzero t with t not -243 and D(t) nonzero, the actual centered J germ has a simple zero. Analyticity, centered value0 and nonzero derivative are all supplied explicitly.

5. Exhaustive centered finite orders. Required: All nonzero finite source points need an actual-map order formula, including the unramified preimage -27 of zero. Constructed: finiteOrder is3 at -243,2 at D roots and1 otherwise. actual_centered_order handles these exhaustive cases. Application: The earlier actualFiniteExpression neighborhood equality transfers the ordinary germ; previously proved exact exceptional orders handle -243 and every D root. Centering uses the actual J(t), shown to equal0 or1728 in the exceptional cases.

6. Meaning of local degree certificate. Required: A local order must be tied to the genuine scheme map and original source/target charts, not just an auxiliary scalar. Constructed: LocalDegreeCertificate stores actual chartPoint source equality, an analytic scalar germ, whole-neighborhood equality of the actual mapPoints with the chosen original target chart, and centered meromorphic order. Application: finite_nonzero_certificate uses the exact denominator map formula. finite_zero_certificate and infinity_certificate use the original numerator-localization cusp formulas, so totalized finite division at zero is never used.

7. All projective scheme-valued complex points. Required: A finite-chart statement does not exhaust the projective source. Constructed: every_point uses the actual finite_or_infinity theorem. The finite coordinate is split into zero and nonzero, with reciprocal infinity handled separately. Application: Every genuine base-preserving complex scheme point has a certificate of order1,2 or3. The finite origin is order3, the reciprocal origin order1, and the nonzero finite branch set is exactly -243 or D(t)=0.

8. Canonical q-disc and completed arithmetic compatibility. Required: Algebraic-chart orders must remain compatible with the already constructed modular completion and actual cusp discs. Constructed: actual_cusp_orders retains the exact existing actualQExpression theorem for every End3, not only two named ends. Application: The same map is finite flat surjective rank4 on the original proper completion, and the preceding rational arithmetic model isomorphism/dense-open embedding and compact analytic map are inherited unchanged. No new charts replace the separately checked original q-disc coordinates.

9. Verification and boundary of branch result. Required: Source drafts need hosted Lean and independent review, and pointwise analytic orders are not automatically a formal scheme divisor identity. Constructed: Three new modules extend80 unchanged sources. Structural/hash/application checks are separate from kernel elaboration; no Lean ran locally. Application: This candidate supplies actual finite-flat global rank4 and exhaustive local chart order certificates. A scheme-theoretic ramification/divisor equality, general quotient/PEL family inputs and the full318/326 arithmetic proof remain separate. No integral extension through3 is claimed.

