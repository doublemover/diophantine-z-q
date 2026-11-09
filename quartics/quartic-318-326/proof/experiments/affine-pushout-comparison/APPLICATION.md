# Exact affine tensor-pushout adjunction mate

Three new sources construct the original module base-change comparison for
arbitrary commutative algebras R to A and R to B. The actual pushout ring is
A tensor_R B. No flatness, reducedness or finiteness assumption is needed.

1. **Original ring square.** `AffineModuleBaseChange318.ring`, `leftMap`
   and `rightMap` are the literal algebra tensor ring and its original
   inclusions. `AffineModuleMate318.ring_square` proves equality of the two
   composites from R, using the actual include-left and include-right maps.
2. **Actual module domains.** `TensorPushoutModule318` quantifies every
   original B-module N with its compatible R action. Its source is
   (A tensor_R B) tensor_B N using the right B algebra action. Its target
   is the actual A tensor_R N with the left A action.
3. **Balanced map and full coverage.** The collapse map is constructed
   by the genuine balanced tensor universal property and sends
   (a tensor b) tensor n to a tensor (b smul n). The balanced equation is
   checked for every tensor, not just asserted on a generating subset.
4. **Actual inverse.** Expansion sends a tensor n to (a tensor 1) tensor n.
   Both inverse laws use full tensor induction and the original balanced
   relations. `equivalence` is an actual A-linear equivalence.
5. **Categorical scalar structures.** `categoricalTensor` reconciles the
   original categorical extension and restriction actions through the
   unchanged `ScalarExtensionTensor318.tensorEquiv`. It does not silently
   replace a restricted module instance with an unrelated algebra action.
6. **Original natural comparison.** `component` and `naturalIso` compare
   exactly extension along the right inclusion then restriction along the
   left inclusion, with restriction from B to R then extension from R to A.
   Naturality is proved for every original B-linear morphism by full tensor
   induction. Both component directions retain explicit pure-tensor formulas.
7. **Original restriction square.** `restrictionSquare` uses the actual
   `restrictScalarsComp` and `restrictScalarsCongr` maps associated to the
   proved ring square. Their underlying maps are identities, with the exact
   structural scalar actions and equality transport retained.
8. **Exact adjunction mate.** `baseChangeMap` is constructed from the
   original right-inclusion adjunction unit, restriction along B over R,
   the original restriction square, and the inverse hom equivalence for
   the original R-to-A extension/restriction adjunction. `baseChangeMap_eq`
   proves this exact map equals the inverse of `component`. Thus its
   invertibility is established for the canonical mate, not merely by
   giving an arbitrary isomorphism of the same two modules.
9. **Next consumer and boundary.** This supplies the tensor-pushout
   base-change prerequisite for converting genuine affine geometric
   overlap data into coalgebra data. That conversion, diagonal/triple
   compatibility, original scheme-sheaf mate identification, arbitrary
   scheme gluing, effective fppf line-stack descent, degree zero,
   representability, Jacobians, polarization and isogeny remain open.
