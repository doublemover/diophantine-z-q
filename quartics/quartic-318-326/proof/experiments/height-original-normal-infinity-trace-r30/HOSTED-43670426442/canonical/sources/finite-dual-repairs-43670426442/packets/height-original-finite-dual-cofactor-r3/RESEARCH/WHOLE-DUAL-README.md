# Genuine whole normalized finite-order dual module

Inactive two-module source continuation; no local Lean, active packet changes or kernel verification.

`TensorFiniteDual318` uses the native finite-projective tensor-dual equivalence to combine two genuine perfect finite-dual pairings. The resulting map is an equivalence with the entire Hom_R(A tensor B,R), not merely a formula on pure generators. Pure-tensor evaluation is proved with the native multiplication order, and three full tensor inductions prove multiplicative/precomposition equivariance for every tensor sum.

`NormalizedOrderFiniteDual318` applies this construction to the actual nested four-root tensor order and the independently reviewed monic-quadratic perfect pairings. It produces a perfect R-linear equivalence from the entire original order A to its genuine finite dual Hom_R(A,R). It then proves that every functional is uniquely of the form y↦lambda(xy), where lambda=perfect(1), with x in the actual order. Thus the generator and the multiplication action are explicit and verified for all elements, not supplied as an abstract duality premise.

The final definition specializes R to V[T] and p_i to the actual normalized d_i(T-a_i). It therefore constructs the actual finite relative dual Hom_{V[T]}(A,V[T]) for the whole normalized model, including bad nonunit twists and residue characteristic2. No root, twist,2 or determinant is inverted. Finite/free instances come from the actual monic quadratic presentations and their tensor products.

This closes the earlier missing four-factor finite-dual construction. It does NOT yet identify this finite dual, tensored with the coordinate differential on the base, with a relative curve dualizing sheaf, prove the fundamental-class/conormal comparison, or compare it with the original maximal regular model. The algebra action is stated through explicit multiplication/precomposition and unique representation rather than a new bundled algebra-module instance. No cotangent/dualizing integral lattice equality, maximal-model section extension, KS210, metrics or GeometricRealization is asserted.

The native quadratic different factor2z and whole cofactor M remain uncanceled in the preceding source batches. Relating the tensor dual generator to those derivation/conormal maps is still separate work. All custom-source copies, imports and native API pins are source-only evidence; future hosted elaboration and axiom checks remain required.
