# Bounded hosted geometry repair

Successor of `height-normalized-valuative-center-r55` at `4d85d68746c3729658dd5f85869f7dd4fc2b505f`. Frozen predecessor sources and evidence remain unchanged. Hosted run [43344479993](https://github.com/doublemover/diophantine-z-q/actions/runs/43344479993) is failure evidence, not acceptance.

## Exact source changes
* `IntegralRationalInfinityMap318`: normalize the original scalar action using an abstract typed ring-map helper; prove rational constants agree using `RingHom.ext_rat`; abstract localization and three-root extensionality before specializing the original nested carriers. The same coordinate and all three signed generators are still required.

## Application contract
1. **Required inputs:** The extensionality argument consumes the entire principal-localized polynomial base and every index in `Fin 3`; the localization helper requires the given principal localization, tensor base change, and a ring equivalence.
2. **Constructed objects:** Retain the original integral infinity order, original overlap, and original Kummer field. No carrier, coefficient, root sign, or hypothesis is replaced.
3. **Index coverage:** The root obligation remains `∀ j : Fin 3`. Rational constants use the uniqueness of ring maps out of `ℚ`, not a selected subset of constants.
4. **Transition maps:** The original infinity-to-overlap map, its original-field embedding, rational presentation equivalence, and tensor right inclusion are unchanged.
5. **Scalars and conventions:** The scalar helper expands the given `CommonBase` algebra action. The original inverse root and ordered quotient formulas are retained; no coefficient or normalization is dropped.
6. **Consumer identity:** `field_restriction` remains equality of the same two full ring homomorphisms, and `infinity_restriction` still compares their values in the original open field. The open-range repair identifies the same original denominator basic open, not an abstract isomorphic chart.
7. **Exceptional cases:** The generic range argument still assumes only its original commutative rings, localization, and equivalence; no field or nonzero-denominator assumption is added. All public declarations retain their signatures.
8. **Downstream scope:** This successor copies the full predecessor module order, replacing exactly `IntegralRationalInfinityMap318.lean`. Every other Lean source is byte-identical. Nested historical metadata is historical only; current intake, inheritance, and bindings govern this successor.
9. **Verification and acceptance:** Source comparison checked signatures, imports, and option lines. Primary APIs are read at pinned Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and bound with exact hosted failure logs. No local Lean ran. Independent source review and the exact hosted strict checks plus recursive axiom audit remain pending. A source/hash/import check is not Lean elaboration or mathematical acceptance; no global arithmetic theorem is claimed.
