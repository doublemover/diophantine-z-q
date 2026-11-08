# Bounded independent review: actual character differential pullback

Decision: ACCEPT the exact eleven-source consuming application bound below. No material objection found. This is a non-author source/application read, with retained strict-check and recursive-audit evidence inspected, not a fresh Lean replay or a blanket review of every predecessor.

Target: recovery-hodge-0358/character-invariant-pullback. Receipt cd6a34418b8dc2fdcb6ce6aa32247857590037c47e1e6d80f012fa61b20d8866; APPLICATION 6648299480887a9518a215cfa3964d1e0367dfc0757a8304cf8947841cc5019e. Reviewer: /root/restart_modular_curve. Author: /root/restart_hodge_gluing.

## Actual-map findings

1. IntrinsicDifferentialPullback318 constructs a derivation from the actual pullback of regular functions followed by the actual source universal derivation. Its Leibniz rule, naturality and vanishing on coefficients use the given entire structure square f ≫ q = p. UniversalSheafDifferentials318.desc is the inverse of the genuine sheafification/universal-derivation equivalence, not an assigned differential map. map_D fixes its normalization on every target open. The pullbackMap is the inverse of the actual Scheme.Modules pullback-pushforward hom equivalence; pullbackMap_adjoint verifies that same map.

2. AffineChartPullbackScalars318 proves the exact appLE/appIso square and then compares scalars using ΓSpecIso naturality. IntrinsicDifferentialSectionPullback318 compares the resulting maps on every universal derivative and closes under scalars and addition via the actual spanning theorem. Thus sectionMap_naturality is equality on the whole Kähler module. It is not just equality on two displayed coordinates or on a generic point. Global restriction follows from sheaf-map naturality.

3. IntrinsicAffineSectionEquiv318 uses the already normalized affine chart isomorphism and tilde.isoTop to prove bijectivity. WeierstrassAffineInvariant318.form is the unique algebraic differential corresponding to the restriction of the actual globally glued invariant. form_section and form_local fix its images on both actual Jacobian charts. No unrelated choice of invariant frame enters the new construction.

4. ContactCharacterDifferentials318 uses each i : Fin 4, the fixed SourceTwistArithmetic318.units, the actual completedMap and its actual over_Q square. The target discriminants are units by the proved nonsingularity of the four published rational models. The result has type global sections of the intrinsic Ω on ContactGlobalSmooth318.Model units. The finite restriction uses CompletedCharacterGlobal318.on_finite and the actual publishedToSource algebra map. I also read the underlying finiteChartMap definition and Spec orientation, rather than treating the name as identification evidence.

5. WeierstrassFiniteDifferentialEquality318 proves equality on the whole finite coordinate ring by the actual section-map injection and sheaf equality on two covering Jacobian opens. The coverage comes from the discriminant-unit Bézout/span identity and prime-spectrum localization surjectivity. On the x-Jacobian open, the differentiated curve equation gives 2y·ω = dx even when y vanishes. On the y-Jacobian open, the actual inverse of 2y gives the same equality. No cancellation of y on the entire ring and no density argument occurs.

6. The original coordinate map sends x to xScale·(t−centroid) and y to yScale·z. CharacterCoordinateDifferentials318 differentiates those exact functions and proves xScale = scaleUnit·yScale. The final normalization applies the genuine algebraic differential map to 2y·ω = dx and cancels only the unit yScale. Therefore the exact result is 2z·finiteForm = scaleUnit·dt on the whole finite source ring. CharacterPullbackNormalization318.intrinsic_finite_equation explicitly transports this identity to the restriction of the actual globally pulled section, with the actual ambient scalar and derivation maps. It is not an alias of a separately assumed proposition.

## Nine application obligations

- Source hypotheses: exact structure square, actual universal differential sheaf and stated commutative-base hypotheses. The smooth invariant-form step requires the actual discriminant unit; all four rational instances supply it.
- Constructed objects: actual global intrinsic differential sections on the complete contact normalization and actual globally glued invariant sections on the completed targets.
- Domain/index coverage: all four indices for the specified fixed twists. Generic helper statements retain their declared hypotheses. Whole source/target schemes for the global map and whole finite charts for the normalization.
- Transition/comparison maps: appLE and ΓSpecIso scalar square, normalized affine section equivalence, full Kähler-module naturality and both Jacobian restrictions were read.
- Consumed-object identity: the finite form is the image of the exact invariant restriction; finite_restrict identifies it with the restriction of the actual global pullback. No substitution of a merely isomorphic form or function field.
- Coefficient conventions: xScale/yScale is scaleUnit, not its inverse. The denominator-free coefficient is scaleUnit; on an open where z is invertible the familiar coefficient of dt/z is scaleUnit/2.
- Local conditions: both Jacobian opens cover by a proved unit-ideal condition. The x-open argument handles the finite branch locus. No reducedness or field-point test substitutes for equality of differentials.
- Exceptional cases: only actual units are cancelled. No inverse z is used. Global regularity including infinity comes from global pullback, while no new infinity-coordinate formula is claimed.
- Downstream scope: supplies four exact regular sections and their normalized restrictions. It does not establish independence, a basis, nonvanishing, a Jacobian/factor or isogeny, polarization, maximal-order action, PEL, Kodaira–Spencer, height, or the final arithmetic conclusion.

## Evidence and authorship boundary

All eleven frozen source bodies and the complete APPLICATION and README were read. The separately listed immediate predecessor interfaces were read to verify actual maps, normalization and hypotheses. Their full historical proof closures retain their own authorship, checks and independent decisions; this report is not blanket reacceptance. The reviewer authored none of these eleven modules and did not edit them. Earlier reviews in the reviewer's torsion/group/analytic lane do not prove any new contact or Hodge claim here.

The reproducible read-only binding script checks 25 exact hashes, including all source bytes, the application, receipt, eight direct dependencies and four predecessor receipts. It verifies eleven recorded strict success markers and inspects all 76 retained recursive axiom entries across eleven target modules, including private/generated declarations and every required endpoint. Only propext, Classical.choice and Quot.sound occur. Some raw multi-source logs preserve an earlier failure of a later module; the receipt identifies each final successful check and the final target audit. No local compile, full-chain replay, shared source edit, or new dependency installation was performed. Hosted integration remains the coordinator's separate evidence.
