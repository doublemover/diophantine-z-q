# Original contact-point section height

Draft only. No Lean compilation has been run locally, as instructed. Hosted strict compilation, recursive private-inclusive axiom audit, and distinct source review are pending. This packet does not alter the accepted progress snapshot or claim the full 318/326 theorem.

## Result and boundary

The seven predecessor modules are copied byte-for-byte from `height-bicanonical-point-r1`, which remains a draft prerequisite. Two new modules connect their actual evaluated J²-scaled bicanonical pair to the existing number-field height consumer:

- `ContactBicanonicalPointHeight318.normalized_height` identifies its absolute projective height with the height of the exact rational coordinate, dividing by the actual degree of the original point field rather than assuming degree sixteen.
- `frameScalar_a0` and `frameScalar_a1` give the exact nonzero common scalar between any two of the four original branch evaluations. `normalized_height_frame_independent` proves that their normalized heights agree. These are statements about this pair of values, not a construction of sheaf transition maps or equality of frame norms.
- `ContactOriginalMetricConsumer318.normalized_original_height` recovers precisely the original homogeneous height `pointHeight u v` by dividing the second actual value by 32. The contact scale is not silently discarded.
- `section_height` applies the actual section inequality to these fixed values. `metricSections` supplies the original consumer's scalars from the actual evaluated global sections. The canonical/Hodge norms, Hodge degree, factor-210 KS equality, and both all-place bounds remain explicit hypotheses. There is no new existence claim for them.

No PEL identification, integral section extension, Petersson norm realization, auxiliary field comparison, or unconditional five-contact bound is proved here.

## Application contract

1. Required objects: the actual `ContactGlobalBicanonical318.tensor` and global sections, evaluated by the original intrinsic branch-frame and original-point maps in the predecessor. The new aliases `a0/a1` use only those values, not arbitrary scalars.
2. Index coverage: every `i,j : Fin 4` is covered. The original five-form nonvanishing supplies all four branch denominators; its infinity form excludes `v=0`. No assertion about evaluation at an omitted contact point is made.
3. Domain and coefficients: the same `RationalContactPoint318.PointField c t` is used throughout, with its original rational algebra and number-field structure. Specialized squareclasses may be dependent; the degree is the actual finrank, never a substituted 16.
4. Comparison directions: evaluation goes from global sections to the original field. The common scalar from frame i to frame j is a0(j)/a0(i), with nonvanishing proved. No base extension, norm map or lattice map is inferred from this scalar identity.
5. Normalizations: J=2765952000 and its square remain in both evaluated values. The projective ratio is t=32u/v. Only the explicitly rescaled pair [a0:a1/32] has height h(u/v). MetricSections still uses [a0:a1] and retains the original log(32) budget.
6. Consumer identity: `metricSections` supplies the exact a0/a1 of this packet to `RefinedContactRealization318.MetricSections`, retaining every original metric hypothesis. It does not replace the section field with an averaging, PEL or isogeny field.
7. Source hypotheses: `SectionHeight318.rational_ratio_height` requires a number field, a nonzero first value and rational ratio; the original point-field instances and actual scaled-section theorems supply them. `rational_section_height` additionally requires both all-place bounds; they are explicitly assumed for these very values.
8. History: actual source read at `docs/sources/quartic_v10.tex`, lines 7015–7088, gives q1=tq0, J² scaling, finite integrality, Petersson bounds, and Yuan's factor 210. This draft formalizes the scalar/height join, not the historical geometric claims. The current manuscript and prior acceptance records remain unchanged.
9. Validation: seven copied sources have byte-for-byte bindings; the source manifest binds all nine modules and their imports. The audit enumerates private/generated declarations recursively. All Lean conclusions remain proposed until hosted checks pass, and independent source acceptance remains pending.

## Versioned CI repair

The prior packet `height-bicanonical-height-r1` is retained unchanged with its failed hosted evidence. Hosted run 42572007531 at commit 48530f6 compiled all seven predecessor modules, then found two elaboration-coherence errors in the first new height module. The exact failed output is pinned in `verification/failed-predecessor-evidence.json`.

Revision r2 uses the theorem `map_ratCast` to identify the original rational algebra map with the field's rational cast. It also defines `fieldDegree` for an abstract field using its canonical rational module, matching the module in the existing number-field height theorem. The former specialized statement accidentally selected the quotient-presentation module instance. The actual field, normalized degree, sections, nonvanishing, frame comparisons and metric obligations are unchanged mathematically; no hypothesis or conclusion is removed. The canonical field degree is still the actual point-field degree, not the generic cover degree 16.

This is a proposed source repair. No local Lean execution or successful hosted r2 check is claimed.
