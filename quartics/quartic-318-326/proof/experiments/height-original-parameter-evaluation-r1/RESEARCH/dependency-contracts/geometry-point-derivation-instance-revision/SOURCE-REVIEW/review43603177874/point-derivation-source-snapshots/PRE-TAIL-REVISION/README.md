# First-order point lifts and actual cotangent evaluation

Inactive source-only construction, uncompiled and independently review-pending. No active packet, resource or compiler change. This advances the previously supplied evaluation functional for the actual normalized finite/reciprocal orders on the nonzero-root domain; it does not construct a regular/maximal dualizing model or global KS map.

## Exact construction

1. `FourRootFirstOrderPoint318` constructs a V-algebra hom from the whole four-root order to TrivSqZeroExt K K. Its polynomial coordinate is (t,1). For a nonzero root z with radicand derivative b the first-order root is (z,b/(2*z)); its square is (z²,b) in characteristic zero. This construction in K does not require 2 or a twist to be a unit of V.
2. `NormalizedFirstOrderPoints318` proves the actual radicand equations before using the whole-order universal map. For the finite polynomial d_i*(X-a_i), b_i=d_i. For the reciprocal polynomial d_i*X*(1-a_i*X), b_i=d_i*(1-2*a_i*w). All four original signed roots are used. No root or discriminant is inverted in the source order.
3. `FirstOrderCotangentEvaluation318` extracts the second component as a derivation with the exact projected point's A-action on K. The native universal Kaehler lift then gives Ω(A/V)→K. The native heterobasic tensor lift gives V⊗[A]Ω(A/V)→K, balanced using the actual A→V→K action. Evaluation on 1⊗Da is precisely the constructed first-order coefficient.
4. `NormalizedCotangentEvaluation318` supplies the full construction for each actual integral chart point f:A→ₐ[V]V. Root values are defined as the images of the actual four generators under A→V→K. Their square equations are proved from `generator_square`, not assumed separately. The exact polynomial evaluation identity and nonvanishing of these generator values are the explicit prerequisites. Whole polynomial-base plus all-four-root ext proves the first-order projection equals that same point on the entire order. It then constructs the integral cotangent functional with no derivation, free-frame or functional premise. Its value on the actual coordinate differential is 1.

## Domain and normalization boundary

The nonzero-root prerequisite is essential to this route. The current original-height setup has an explicit hn excluding zero radicands. Original signed-root square identities and normalized rescaling identities are retained as primary evidence for the planned specialization, but the complete automatic adapter from hn and `chart_center_alg` to this bundle's hf/hn has not yet been formalized. This is not an all-branch-point theorem. The earlier chart-input bundle covers those points more broadly; it has not been weakened.

The finite functional normalizes DT=1. The reciprocal functional normalizes Dw=1, not Dt=1. The required original-parameter relation is dw=-t^-2 dt when w=1/t. No identification with the original rational branch frame is asserted merely because both are one-dimensional. The original-root sign choices are retained, and the derivative components are forced by those signs and the literal equations.

## What remains

This constructs an actual candidate evaluation map, rather than repackaging that map as an assumption. It does not produce lifts of the original two quadratic sections into the naive cotangent tensor square, nor prove that such lifts exist on all these possibly singular orders. In particular finite generation of an evaluated cotangent image does not identify it with the maximal-model dualizing/bicanonical lattice. The field-valued derivative can have denominators at bad places; these have not been discarded or replaced by an integral-unit hypothesis.

The previously frozen image/frame consumer is retained as pending-review primary context only. It still requires the original section lifts and their exact original-frame evaluations. Regular/maximal model identification, the correct dualizing comparison, Hodge determinant, native KS lower image, metric pullback and finite-height inputs remain separate. No degree/defect bound or GeometricRealization follows here.

## Provenance and checks

The proposed inactive closure is published center-r68's exact 96 sources plus these four in dependency order. Project primaries are pinned to 57227e167abe49436d651b932ff75d5bdf9b5898; native APIs to Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Public native API responses and Git blob identities are retained. Static hashes/imports/no-admission checks and the repository audit self-test do not establish Lean elaboration or source acceptance. Independent review is required; no local Lean was run.

## Explicit point-instance correction

This separate draft preserves the previous frozen bundle at geometry-point-derivation-audit and its complete Library backup. Independent source review found hidden-f local instance declarations whose type did not determine their point parameter. FirstOrderCotangentEvaluation318 now spells out fixed-f letI algebra actions in affected types and bodies, and the exact original tower proofs in bodies. This is a source-level elaboration-risk correction, not a hosted diagnosis or proven performance repair. Every actual map, full domain, supplied point/projection proof and derivative formula is unchanged. Other three source files are byte-identical. The original raw APP/source and exact diff are retained; no previous review is promoted to acceptance of this revision.
