module
public import OriginalAffineParameterSquare318
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace OriginalAffineParameterPullback318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A B S : CommRingCat.{u}) [Algebra R A] [Algebra R S] (f : A ⟶ B)
local instance : Algebra R B := (f.hom.comp (algebraMap R A)).toAlgebra
local notation "AS" => OriginalAffineParameterSquare318.source R A S
local notation "BS" => OriginalAffineParameterSquare318.target R A B S f
local notation "i" => OriginalAffineParameterSquare318.sourceMap R A S
local notation "k" => OriginalAffineParameterSquare318.targetMap R A B S f
local notation "g" => OriginalAffineParameterSquare318.chartMap R A B S f

lemma ring_square : f ≫ k = i ≫ g := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (1:S) ⊗ₜ[R] f.hom a =
    Algebra.TensorProduct.map (AlgHom.id R S)
      (OriginalAffineParameterSquare318.coefficientMap R A B f) ((1:S) ⊗ₜ[R] a)
  rw [Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
  rfl

/-- The literal parameter tensor square is a ring pushout. Both larger
squares are the canonical tensor pushouts, so cancellation supplies the
right-hand square without a flatness or residue-field hypothesis. -/
lemma pushout : IsPushout f i k g := by
  let a : R ⟶ A := CommRingCat.ofHom (algebraMap R A)
  let s : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
  let l : S ⟶ AS := CommRingCat.ofHom (algebraMap S AS)
  let r : S ⟶ BS := CommRingCat.ofHom (algebraMap S BS)
  have hr : l ≫ g = r := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact OriginalAffineParameterSquare318.source_coefficient R A B S f x
  have ht : IsPushout a s i l := (CommRingCat.isPushout_tensorProduct R S A).flip
  have ho : IsPushout (a ≫ f) s k (l ≫ g) := by
    rw [hr]
    exact (CommRingCat.isPushout_tensorProduct R S B).flip
  exact ho.of_left (ring_square R A B S f) ht

lemma pullback : IsPullback (Spec.map k) (Spec.map g) (Spec.map f) (Spec.map i) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (pushout R A B S f)

instance chart_open [IsOpenImmersion (Spec.map f)] : IsOpenImmersion (Spec.map g) :=
  MorphismProperty.of_isPullback (pullback R A B S f) inferInstance

/-- The actual parameter chart image is precisely the inverse image of
its original affine-open image, not a merely pointwise guessed cover. -/
lemma chart_range [IsOpenImmersion (Spec.map f)] :
    (Spec.map g).opensRange = (Spec.map i) ⁻¹ᵁ (Spec.map f).opensRange := by
  simpa only [Scheme.Hom.preimage_top,Scheme.Hom.image_top_eq_opensRange] using
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (pullback R A B S f) ⊤
end OriginalAffineParameterPullback318
