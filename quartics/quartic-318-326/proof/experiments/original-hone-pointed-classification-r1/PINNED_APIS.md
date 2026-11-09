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

Additional exact Mathlib Scheme.lean declarations read at the same pinned ref:
```lean
theorem comp_appTop {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).appTop = g.appTop ≫ f.appTop := rfl
lemma ΓSpecIso_inv_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv ≫ (Spec.map f).appTop :=
  SpecΓIdentity.inv.naturality f
```
The latter exact direction is used for BOTH tensor projections, after the
original affineIso inverse map on global sections. It proves the canonical
section map is the same map as the tensor inverse, not merely that the two
rings admit some isomorphism.

Further primary APIs read at Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679:
- AlgebraicGeometry/Pullbacks: Scheme.pullback_map_isOpenImmersion preserves
  open immersions in the actual pullback.map; third map is mono.
- CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic: IsPullback.of_right
  cancels the right Cartesian square from the original outer square.
- AlgebraicGeometry/Restrict: Scheme.Hom.isoOpensRange and hom_ι/inv_comp
  identify the literal original inclusion with its entire image; Opens.ι_image_top.
- AlgebraicGeometry/Scheme: app_eq_appLE, appLE_comp_appLE, appLE_map,
  map_appLE, and comp_preimage retain all original coefficient maps.
- AlgebraicGeometry/AffineScheme: IsAffineOpen U is defined as IsAffine U.

Accepted original producer OpenPullbackStructure318.opens_eq identifies the
entire image in the actual Cartesian square, not a selected refinement.
Accepted UnitCocycleSubopens318.transition_reverse proves reversal on every
common subopen. The Bool extensionality consumer uses it on the whole reversed
overlap and uses the actual presheaf identity restriction, including empty opens.

Additional exact declarations read at the SAME pinned Mathlib ref:
AlgebraicGeometry/Morphisms/Affine.lean:
```lean
lemma IsAffineOpen.inf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V)
```
AlgebraicGeometry/Morphisms/Separated.lean:
```lean
protected class Scheme.IsSeparated (X : Scheme.{u}) : Prop where
  isSeparated_terminal_from : IsSeparated (terminal.from X)
```
The original proper/separated rational structure maps and the affine rational
base imply separatedness of the original terminal map by composition.
Its original closed diagonal is affine, so the exact IsAffineOpen.inf input
is supplied for the actual source and all five original targets.

The original accepted LineFrameIsoCocycle.cocycle_eq and LineFrameGauge.equivalent
are read at the exact repository sources. They compare actual original frames
and module-sheaf isomorphisms. Their outputs are not abstract cocycle labels.
