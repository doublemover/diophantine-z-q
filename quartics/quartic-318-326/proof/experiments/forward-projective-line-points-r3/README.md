# Actual projective-line points and compact analytic comparison

Status: revised hosted-CI candidate. The predecessor failed at its bundled
compact-biholomorphism constructor after its first 36 modules passed. These
instance-scoping repairs require a fresh hosted check and distinct review.
No local Lean build, kernel audit, proof acceptance or baseline promotion is claimed.

This candidate extends the restored projective-line field-point drafts to an
actual complex analytic manifold on base-preserving scheme morphisms
Spec(C) → ProjectiveJLine318.scheme Q. Its topology is generated independently
by the original two algebraic polynomial-evaluation maps. Its inverse complex
charts are proved to be exactly those maps, including both origins.

It then composes the original compact level-three comparison with this explicit
projective-point realization. Every original point and both actual cusps have
exact equalities of scheme-valued points, and the final analytic equivalence
retains precisely this composite. The target coordinate is the original T
parameter; this does not silently identify it with the modular j map.

## Exact application contract

1. Actual points and fixed coefficient map. Required: Base-preserving morphisms from Spec(C) to the exact original Proj over Q, with no arbitrary coefficient-field map. Constructed: Points is the subtype of actual scheme morphisms satisfying the original structure-map equation; chartPoint is literal polynomial evaluation followed by JLineAtlas318.chart. Application: The equality over Spec(R) is carried as a field of Points. Every factored morphism is converted using Spec.homEquivAlgHom, so polynomial algebra-hom extensionality identifies its coordinate without forgetting the coefficient map.

2. Coverage on all scheme-valued points. Required: Every field-valued morphism, including infinity, must factor through one of the actual two affine charts. Constructed: point_factors_chart uses the original open cover and the singleton field spectrum; every_point_in_chart recovers an actual evaluation coordinate. Application: The image of the entire field spectrum lies in the selected chart because that spectrum is a subsingleton. IsOpenImmersion.lift factors the morphism itself. This is not merely coverage of closed geometric points or generic parameters.

3. Exact algebraic reciprocal transition and exceptional point. Required: Reciprocal transition on exactly the invertible-coordinate overlap and a genuinely distinct infinity point. Constructed: unit_overlap is the same scheme-morphism equality as JLineOverlap318.unit_chart_overlap; chart_zero_preimage_one is the original basic open X≠0. Infinity has empty preimage in the finite chart. Application: For any field coordinate, zero in chart 0 is the infinity point; every nonzero coordinate there converts by a unit to chart 1 at its reciprocal. Finite chart injectivity and disjointness from infinity prove pointMap bijective on every point, with no cardinality shortcut.

4. Independent complex topology. Required: The topology on actual scheme-valued points must arise from original algebraic charts, not from the modular comparison. Constructed: complexPointTopology is coinduced from the disjoint union of the two original algebraic evaluation maps. sphereCover is the independent finite/reciprocal sphere cover. Application: sphereCover is continuous, open and surjective. pointMap_sphereCover identifies the two cover maps exactly. The quotient-map criterion and coinduced-domain criterion prove both continuity directions for pointHomeomorph. The topology definition uses neither Filled nor compactHomeomorph.

5. Exact algebraic inverse charts and overlap domains. Required: Actual complex charts must have the two original algebraic evaluation maps as inverses, including both origins. Constructed: pointChart lifts the independent sphere charts along pointHomeomorph. finite_pointChart_symm and infinity_pointChart_symm identify the inverses with chartPoint 1 and chartPoint 0 for every complex coordinate. Application: Both chart targets remain the whole complex plane. point_transition cancels the exact homeomorphism in both directions, retaining the independent reciprocal overlap. Thus the manifold is identified with actual algebraic evaluations rather than an unidentified transported atlas.

6. Full target analytic-manifold construction. Required: The exact existing topology and all scheme-valued points must admit compatible analytic charts. Constructed: pointChartedSpace uses the finite chart at every finite point and reciprocal chart at infinity; point_isManifold proves analytic groupoid compatibility. Application: Source membership and atlas membership follow through the actual bijective pointHomeomorph. The copied sphere compatibility theorem applies on the exact lifted transitions, with no freeness, smoothness or local-inverse assertion inferred from topology alone.

7. Exact sphere analytic equivalence. Required: Both directions of the previously proved point homeomorphism must be analytic for these particular charts. Constructed: point_contMDiff and point_symm_contMDiff reduce the exact maps to the same chosen-chart cancellation germs; pointBiholomorph retains pointHomeomorph.toEquiv. Application: chart_cancel_analytic applies only at a point in the open chart target and uses the partial inverse there. The source and target chart expressions are explicit. No globally valid cancellation of a partial chart or alternate equivalence is assumed.

8. Original compact modular consumer and cusp assignment. Required: The actual compact source and its original parameter must map to the same scheme-valued target points on every original point and both cusps. Constructed: compactPointHomeomorph composes the unchanged compactHomeomorph with pointHomeomorph. Its original-point formula is chartPoint 1 at quotientParameter; infinity and zero cusps are chartPoint 0 at zero and chartPoint 1 at zero. Application: The three exact evaluation identities consume compactHomeomorph_original, compactHomeomorph_infinity and compactHomeomorph_zero. Diffeomorph.trans composes the exact previously specified maps, so compactPointBiholomorph_apply equals this same homeomorphism. The source atlas still has the independent original quotient and genuine q-disc germ criteria. No arithmetic descent or j-map compatibility is concluded.

9. Verification, history and boundaries. Required: Copied sources must remain identifiable, all changed applications need hosted kernel checks and distinct review, and arithmetic claims must remain bounded. Constructed: The original r2 closure carried 38 complex-atlas sources, three restored projective-point drafts and three analytic bridge modules. This r3 changes only the instance-scoping bodies of three constructors and retains the other 41 sources byte-identically. All 44 sources are hashed and ordered for the existing hosted experiment workflow. Application: The first 31 complex-source predecessors have separate bounded historical germ/topology review. None of that acceptance verifies the newer atlas, projective point classification, target analytic atlas or changed consumer. The previous hosted attempt passed its first 36 sources and failed at compactBiholomorph due to a missing ChartedSpace instance during record elaboration. This revised packet is uncompiled and unaccepted; no pass receipt is fabricated. It supplies a concrete chart realization for the explicit projective line if checked, not a general analytification functor, algebraic realization of the modular j map, PEL/universal-family identification, field-of-definition result or final arithmetic witness.

## Source history and next checks

This revision retains 41 of the 44 r2 sources unchanged. Exactly three
constructor bodies install the topology/chart instances already stated in their
types: compactBiholomorph, pointHomeomorph and pointBiholomorph. No mathematical
statement, coordinate, map or chart definition has been replaced. The three bridge modules first introduced in r2 are
ProjectiveLineComplexAtlas318, ProjectiveLineBiholomorph318 and
ActualThreeProjectivePoints318. The complete 44-source closure allows hosted CI
to check the exact consumers against the verified progress baseline.

Run only the existing hosted Progress Lean experiment workflow for Lean checks.
The coordinator owns activation in packets.json. This directory contains no
local-build scripts. Structural packet validation is not a Lean proof check.

A general scheme analytification functor, compatibility with the actual modular
j morphism, universal-family and quaternionic PEL realization, arithmetic
field-of-definition identification and the final 318/326 arithmetic theorem
remain separate. The pending proof supplies only this explicit two-chart
complex realization of the actual projective-line scheme-valued point set.

## Exact failed-stage preservation

The prior r2 packet remains unchanged. previous-failure/ preserves its exact
RESULT and compact-biholomorphism error log from hosted run 42572007531 at
commit 48530f6. The first 36 modules passed individual strict checks, including
ActualThreeComplexAtlas318 and ActualThreeCanonicalAnalytic318. The packet did
not reach its recursive audit or later projective-point modules. These partial
checks are not whole-packet acceptance.

The failure occurred because the dependent letI binders in a definition's type
did not install the local instances needed while elaborating its structure
literal. The repaired definition uses a by block, installs the same instances,
and returns the same equivalence and analytic proofs. The identical vulnerable
construction pattern is repaired in the later point homeomorphism and point
biholomorphism as well.
