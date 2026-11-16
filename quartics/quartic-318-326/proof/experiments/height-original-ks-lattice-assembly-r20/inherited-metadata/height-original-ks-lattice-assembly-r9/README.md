# Exact hosted geometry target-normalization repair

Successor of `height-original-ks-lattice-assembly-r8` at `58753ec5f3b41268c5ceedae5264593b4f2aa0de`. Frozen predecessor evidence is not rewritten. Hosted run [43519890754](https://github.com/doublemover/diophantine-z-q/actions/runs/43519890754) supplies failure evidence, not acceptance.

## Observed frontier

Center r57 passes 41 module commands and fails only at IntegralRationalInfinityMap318 lines109/121 when the proved hX/h equalities are checked against composite-map targets. Lattice r8 passes IntegralOriginalInfinityEmbedding318 (4.727 seconds) and then fails only at IntegralOriginalChartsProperCover318 line14 because rw cannot find an equation theorem for originalSourceChart. The rational-map change in lattice is propagation of the center diagnostic; lattice has not reached that module. No recursive packet audit has passed.

This successor changes exactly `IntegralRationalInfinityMap318.lean`, `IntegralOriginalChartsProperCover318.lean`. Rational-map repair normalizes the exact target composite via RingHom.comp_apply and names the original coordinate/root before consuming the unchanged hX/h witnesses. Proper-cover repair exposes exactly the originalSourceChart composite and directly applies the native isomorphism-precomposition range theorem.

## Application contract

1. **Required inputs:** Same ring/localization/equivalence inputs and original field. No new public hypothesis or trusted comparison premise.
2. **Constructed objects:** Same original integral infinity order, full overlap and original Kummer field. Target normalization changes only the presentation of the exact existing expressions.
3. **Coverage:** Rational constants, polynomial X, the entire principal-localized base and every ordered j : Fin 3 root remain required by the same private extensionality helper. No coverage obligation is removed.
4. **Transitions:** originalFieldEmbedding, infinityMap, rationalOrderEquiv and originalEmbedding retain their definitions. When the chart repair is present, originalSourceChart uses the same Spec of the same finite comparison inverse followed by finiteChart.
5. **Scalars and signs:** The signed pivot root, inverse unit and ordered quotient roots remain unchanged. No equality is replaced by its square or by a new scalar map.
6. **Consumer identity:** field_restriction still identifies the exact full ring maps, then infinity_restriction uses the same original open-field injection. The cover proof still consumes the whole original finite source and restricted original infinity chart.
7. **Exceptional cases:** No field or nonvanishing hypothesis is added to generic chart coverage. No prime, index, point or branch is excluded.
8. **Downstream preservation:** Full predecessor source list and order are retained. Only the listed proof scripts differ; public declarations, imports and resource options are unchanged. Older evidence directories and inherited-metadata are historical, not new approvals.
9. **Verification boundary:** Source review and tooling evidence are not Lean acceptance. Hosted strict replay and recursive axiom audit remain pending. No local Lean/Lake run, whole arithmetic theorem claim or manuscript acceptance.
