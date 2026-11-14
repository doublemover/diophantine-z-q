# Exact hosted geometry abstract-carrier and scalar-instance repair

Successor of `height-original-ks-lattice-assembly-r9` at `a2d615a4183174328321ea21d60879add229de3a`. The predecessor is frozen. Hosted run [43534276453](https://github.com/doublemover/diophantine-z-q/actions/runs/43534276453) is observed evidence, not acceptance of these candidates.

## Observed frontier and bounded change

Center r58 records41 successful module commands, then recursion at IntegralRationalInfinityMap318 lines110/125 while changing concrete coordinate/root targets. Lattice r9 records60 successful module commands, including IntegralOriginalChartsProperCover318, before LocalizedTensorRestriction318 rejects targetAlgebra because f cannot be inferred from Algebra A T. Remaining lattice errors cascade from the missing scalar structure. Neither packet completed its recursive audit.

This successor changes exactly `IntegralRationalInfinityMap318.lean`, `LocalizedTensorRestriction318.lean`. The rational repair performs chart-coordinate/composite normalization in a private theorem with abstract intermediate and target rings, then specializes it to the SAME three maps and consumes the SAME hX/hroot witnesses. When present, the tensor repair names the SAME f-induced algebra and explicitly installs it in each definition and proof instead of registering an instance with an uninferable map argument. The rational change in lattice is propagated from the center diagnostic, not a claimed observed lattice failure.

## Application contract

1. **Required inputs:** Same rational chart, actual intermediate algebra/map and original field witnesses. The private wrapper requires the algebra already present in infinityMap. Tensor localization still requires only the same rings, A-actions, element x, localization L and IsUnit image under f; no Algebra A T hypothesis is added.
2. **Constructed objects:** Same infinity order, localized coefficient base, original overlap and original Kummer field. Tensor targetAlgebra is exactly (f.comp (algebraMap A B)).toAlgebra, not an alternative scalar action.
3. **Coverage:** rational_order_ext still proves equality on rational constants, polynomial X, the full localized base and every j : Fin3 ordered root. The new wrapper discharges those same premises. No prime/index/branch or tensor factor is omitted.
4. **Transitions:** originalFieldEmbedding, infinityMap, rationalOrderEquiv, originalEmbedding remain unchanged. Tensor baseMap is the original Away.lift of f composed with the original base map; rightMap is f; lift is the original TensorProduct.lift of those maps.
5. **Scalars and signs:** Same signed pivot root, inverse unit and ordered ratio roots. No root is squared away. Explicit letI uses the named original scalar structure identically in result types and bodies.
6. **Consumer identity:** field_restriction still identifies the exact full maps and infinity_restriction uses the original field injection. IntegralOriginalCommonRestriction318 still consumes the same lift and lift_right through the same finiteBaseChange inverse.
7. **Exceptional cases:** Generic tensor restriction remains over arbitrary commutative rings with the exact original invertibility condition. No new field or nonvanishing premise, excluded point, or replacement comparison assumption.
8. **Downstream preservation:** Full predecessor source set/order retained; ancillary new/revised/reused/unchanged lists are recomputed from exact bytes. Public theorem statements and lift ring-hom type, imports and resource options unchanged. Tensor baseMap/rightMap type text explicitly names the original scalar structure and targetAlgebra becomes a named instance-reducible definition rather than invalid instance registration; do not mistake that for unchanged declaration text. Older evidence and inherited metadata remain historical.
9. **Verification boundary:** Independent source/propagation review is distinct from hosted elaboration and recursive axiom audit. In particular the abstract-carrier wrapper's recursion behavior remains unverified until hosted. No local Lean/Lake run or arithmetic-theorem/manuscript acceptance.
