# Actual compact level-three complex curve and its biholomorphism

Status: uncompiled hosted-CI candidate. Strict Lean checks, recursive axiom audit
and distinct non-author application review are pending. No local Lean build was run.

This candidate packet is intended to supply an actual complex analytic atlas on the unchanged compact
filling of the original level-three quotient, and a complex analytic equivalence
with an independently constructed standard complex sphere. Its canonical-source
comparison is explicit: scalar holomorphic germs for the new bundled manifold
are precisely the original quotient-pullback germs, including elliptic points,
and precisely the actual original selected q-disc germs at the added cusps.
The source atlas is therefore not left as an unidentified transported structure.

## Exact application contract

1. Independent target and topology. SphereInversion318 constructs inversion on the existing OnePoint complex plane, exchanging zero and infinity and using literal reciprocal on nonzero finite points. Its two continuity checks at zero and infinity use the actual neighborhood and cocompact filters, not a topology transported from the modular source. The involution supplies the independent target homeomorphism. No modular quotient or chosen parameter enters this construction.
2. Full target chart domain. SphereCharts318 constructs the finite chart on the image of the complex plane and the reciprocal chart containing infinity. Both target coordinate domains are the whole complex plane. The chosen chart uses the finite chart at every finite point and the reciprocal chart at infinity, with actual source membership and atlas membership proved. Thus zero, infinity and every finite exceptional value are included.
3. Independent target analytic compatibility. SphereComplexCurve318 proves both mixed overlap domains are exactly the nonzero complex numbers, and both coordinate changes there are the literal reciprocal. Analyticity of inversion off zero gives the required complex analytic groupoid compatibility in both directions; the same-chart transitions are handled by the actual groupoid theorem. This yields the independently defined sphere IsManifold structure.
4. Original source and exact transitions. ActualThreeComplexAtlas318 uses the already constructed actual Filled quotient topology, not a new topology on an equivalent set. Source charts are lifts of the independent sphere charts along the inverse of the unchanged compactHomeomorph. Their forward formula is exactly target-chart after that compact map. The two original maps cancel in transitions, and the resulting overlap map is exactly the target overlap. The atlas covers all original points and both added cusps, and yields IsManifold with the previously proved compact, Hausdorff and second-countable properties of the same Filled.
5. Bundled scalar germ criterion. ActualThreeCanonicalAnalytic318.contMDiffAt_iff_coordinate derives the actual bundled ContMDiffAt analytic scalar criterion by the primary source-chart characterization. It uses the exact chosen target chart, its inverse, the unchanged compact map and the unchanged function on Filled. The conversion between complex analytic germs and ContDiffAt at analytic regularity is in the actual complex normed-space setting, not a real smoothness replacement.
6. Canonical original quotient consumer. original_canonical_iff identifies the new bundled scalar holomorphy at every original point with the independently defined QuotientHolomorphicAt condition for pullback along the original quotient map. That condition quantifies over every original representative. The predecessor's critical-point descent proves the equivalence also at elliptic points, and the present application uses the exact finite target chart and exact original compactHomeomorph value. No freeness assumption at level three is added.
7. Canonical actual cusp consumer. cusp_canonical_iff identifies the bundled scalar holomorphy at every actual End 3 origin with analyticity of the same function pulled back along its actual sourceDisc. Exhaustion is the actual identity/S end classification, not a replacement two-element index type. At infinity the chosen target chart is reciprocal, and at the other end it is the finite chart. The predecessor's exact q-to-sphere expressions and order-one inverse germs supply both implications. The selected representative and its genuine width are retained.
8. Exact global analytic equivalence. ActualThreeBiholomorph318 proves analytic regularity of the unchanged compactHomeomorph and its inverse using the exact source/target charts. The coordinate expressions are identity germs on actual open chart targets, using the partial-homeomorphism right inverse there, rather than a false global cancellation of partial charts. compactBiholomorph packages precisely the original equivalence, not an arbitrary complex-curve isomorphism. Combined with the two canonical-source criteria, this identifies the actual original quotient-and-q-disc complex structure with the independent standard sphere.
9. Verification, history and excluded arithmetic applications. The thirty-one predecessor sources are byte-identical to the separately reviewed holomorphic-descent packet. The six restored atlas sources and the new global consumer require first hosted strict replay, recursive private-inclusive standard-axiom audit and distinct application review. No pass receipt or acceptance is claimed. Prior accepted formulas, exceptional fibers, actual cusp assignments and compact topology remain unchanged. This is an analytic compactification comparison, not an arithmetic scheme analytification theorem, an identification with a PEL coarse/fine moduli scheme, a universal family comparison or a marked-field degree calculation. No final arithmetic height theorem or manuscript incorporation is inferred.

## New all-points consumer

ActualThreeGlobalHolomorphy318 defines SourceHolomorphic using only the original
quotient pullback at every original point and the genuine selected q-disc germ
at every actual end. contMDiff_iff_source uses original_or_cusp exhaustion to
prove that this is exactly global bundled analytic regularity.
targetExpression_contMDiff_iff_source identifies these original source functions
with globally analytic functions in the independent sphere atlas via the exact
compactHomeomorph. It does not infer holomorphy from a generic open subset.

The 37 inherited sources are byte-identical to the preserved r1 draft. The first
31 also match the independently reviewed holomorphic-descent packet. Earlier
acceptance does not extend to the six restored atlas drafts or this new consumer.
This r2 packet has no local-build or absolute-path freeze scripts; the existing
Progress Lean experiment workflow owns compilation. The coordinator may activate
forward-three-complex-atlas-r2 in packets.json after source review.

## Remaining realization

If the pending checks and review succeed, the actual complex curve and original
compact parameter will be compared at the bundled analytic-manifold level, with
source germ meaning supplied by the separate original/cusp criteria.
An algebraic/arithmetic model analytification identification and the actual
quaternionic PEL and universal-family realization remain separate obligations.
The standard target here is the independently charted OnePoint complex sphere;
no unproved topological or analytic identification with an arithmetic project's
projective-line scheme is used.
