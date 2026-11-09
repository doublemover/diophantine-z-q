# Exact primary APIs

Mathlib commit56a005855ea17e0b0958f73ec801ae140b0a1679, read at the exact ref.

- Algebra/Module/Projective.lean: Module.projective_lifting_property lifts a linear map through a SURJECTIVE linear map, with the original projective target module.
- LinearAlgebra/TensorProduct/Quotient.lean: TensorProduct.quotTensorEquivQuotSMul P I identifies (S/I) tensor P with P/(I smul top); quotTensorEquivQuotSMul_mk_one_tmul fixes the actual 1 tensor x representative.
- RingTheory/Ideal/Quotient/Operations.lean: Ideal.quotientKerAlgEquivOfSurjective for the actual Algebra.ofId S R and its proved surjectivity.
- RingTheory/Ideal/Span.lean: mem_span_singleton' states x in span{y} iff there exists a with a*y=x. The commutativity conversion is explicit in ring_kernel.
- RingTheory/Ideal/Operations.lean: Submodule.ideal_span_singleton_smul (r)(N) states (Ideal.span{r}) smul N = r smul N.
- Algebra/Module/Submodule/Pointwise.lean: mem_smul_pointwise_iff_exists (m)(a)(S) states m in a smul S iff there exists b in S with a smul b=m.
- RingTheory/Flat/EquationalCriterion.lean: Module.Flat.projective_of_finitePresentation [Flat R M] [FinitePresentation R M] : Projective R M.

The two OriginalLineAffineModel/BaseChange sources are exact PENDING experiment
producers, not baseline-accepted sources. Their original canonical tilde-Gamma
counit, actual original pullback, and literal extendScalars remain the consumed
maps. The producer confirmed unchanged hashes in its latest revision.

Additional exact-ref APIs read for this application:
- Algebra/DualNumber.lean: DualNumber.lift constructs an algebra map from a specified coefficient algebra map and commuting square-zero element. lift_apply_inl and lift_apply_eps retain both generators. algHom_ext and TrivSqZeroExt.algHom_ext' justify both inverse identities.
- RingTheory/TensorProduct/Basic.lean and Maps.lean: original includeLeft, includeRight, lift, lift_tmul and ext retain BOTH scalar-extension factors.
- Algebra/Algebra/Equiv.lean: AlgEquiv.ofAlgHom f g requires f.comp g=id and g.comp f=id, in that order.
- AlgebraicGeometry/Pullbacks.lean: pullbackSpecIso is the literal categorical pullback of both original Spec algebra maps; inv_fst and inv_snd identify its original projections with Spec of includeLeft/includeRight.
- AlgebraicGeometry/AffineScheme.lean: Scheme.isoSpec is asIso X.toSpecGamma for the original affine scheme, not an arbitrary chosen replacement.

Exact GammaSpecAdjunction.lean declaration read at the pinned ref:
```lean
lemma Spec.map_surjective {R S : CommRingCat} :
    Function.Surjective (Spec.map : (R ⟶ S) → _) := by
  intro f
  use Spec.preimage f
  simp
```
The same file constructs Spec.fullyFaithful from the actual Gamma-Spec
adjunction and its isomorphic counit. The consumer applies this to the ACTUAL
X.isoSpec.inv followed by p, so the recovered map has direction R→Gamma(X).
