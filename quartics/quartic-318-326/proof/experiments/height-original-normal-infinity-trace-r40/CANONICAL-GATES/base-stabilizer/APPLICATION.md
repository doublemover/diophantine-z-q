# Original norm-one base stabilizer: explicit matrix wrapper

1. required_inputs

Unchanged fixed_implies_sign takes every actual order unit u with original reduced norm one, arbitrary complex τ in the open upper half-plane, and its actual unitParameter fixed-point equality. scalar_of_extreme_trace retains all matrix, determinant, fixed-line, sign-square and trace hypotheses. No abstract stabilizer, projective surrogate or scalar conclusion is supplied.

2. constructed_objects

Only two simp-only lists gain the existing exposed unitMatrix definition. Its complete producer defines unitMatrix ρ O u as exactly ρ((u:O):B). For the actual representation and original order this produces precisely representation((u:order):B), which the existing representation_injective goal requires. No new map, witness or declaration is introduced.

3. index_and_domain_coverage

Both plus-one and minus-one trace branches are retained. Every original order unit and every upper-half-plane fixed point satisfying the original hypotheses remain covered. There is no finite sampling, selected unit subgroup, boundary point substitution or restriction of the trace obstruction.

4. transition_maps

Unfolding unitMatrix explicitly aligns hm with the representation image equality. Existing one_smul and map_one handle the positive branch; existing neg_one_smul, map_neg and map_one handle the negative branch. The same injective rational quaternion representation then yields the same original quaternion equality, lifted through Subtype.ext and Units.ext to u=1 OR u=-1.

5. dependency_chase

The actual determinant and fixed-line trace bounds, newly passing exact mod5/mod7 TraceObstruction, scalar_of_extreme_trace construction and final extensionality path are unchanged. The logged mismatch is specifically unitMatrix representation order u versus representation ↑↑u after scalar simplification. Explicitly unfolding the existing wrapper addresses that conversion without altering any mathematical premise.

6. public_signatures

Exactly two existing simp-only argument lists change. Full theorem statements, definition values, imports, namespace, maxHeartbeats1500000, all other proof lines and the unused-simp warning are left intact. No admission, axiom, helper, exposure change, extra assumption, diagnostic or resource workaround.

7. consumer_comparison

PELNormOneBaseAction.stabilizer_sign applies the unchanged theorem to the actual normOneUnits action and τ.property. PELEffectiveNormOneAction continues to identify exactly the scalar-sign kernel and obtain freeness of the image action. The repair neither assumes those downstream conclusions nor changes the original action, quotient or signs. Six complete actual producer/consumer bodies and exact native simplifier source are bound.

8. limits_and_policy

Own15d/run43817651313 character37 has115 full passes then BaseStabilizer failure1.770s and1053 unreached; trace37 separately has115 passes then failure2.070s and1388 unreached. Both own results/intakes/logs and identical failed copies were reconciled at15d and currente51. No outcome is borrowed. No infinity propagation, local Lean, upload, user computer, main edit or new mathematical research.

9. acceptance_boundary

This is an uncompiled bounded correction of two observed representation-wrapper mismatches. Source/API review and separate own-receipt current propagation gates are required before immutable successors. Source rationale is not hosted whole-module success, recursive audit, whole-packet acceptance, snapshot promotion or a full arithmetic theorem claim.

