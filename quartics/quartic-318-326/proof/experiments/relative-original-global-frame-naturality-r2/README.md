# Native overlap scalar-tower repair

Bounded successor to global-frame-naturality-r1.1162 sources,1161 exact copies. The sole proof change is ContactOriginalRelativeOverlapSpan318's rational/Laurent/native-left-tensor scalar tower.

Hosted316 rejected the previous algebraMap extensionality proof because it produced generic Algebra.toSMul actions while the literal original overlap uses Laurent AddMonoidAlgebra action and TensorProduct.leftHasSMul. The new proof checks the requested native smul_assoc directly by TensorProduct induction. On pure tensors it reduces all three native scalar actions by smul_tmul' and uses scalar associativity on the left Laurent factor. On sums it uses smul_add and the induction hypotheses. Thus no alternative module carrier, ring map, scalar normalization, assumption or budget is introduced.

All classifying-map, inverse, naturality and universal-frame sources are exact predecessor bytes. Fixed-line functor scope remains unchanged, not Picard/Jacobian representation. Raw first-order factor8 unchanged.

No local Lean or profiling. Source/static validation and distinct review only; hosted elaboration pending.
