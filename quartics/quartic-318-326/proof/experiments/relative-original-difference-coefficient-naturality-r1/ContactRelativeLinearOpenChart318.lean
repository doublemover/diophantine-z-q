module
public import ContactOriginalLinearOpenChart318
public import RelativeOriginalAffineChart318
public import VaryingSourceCoefficientPullback318
public section
noncomputable section
namespace ContactRelativeLinearOpenChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ)
  (l : MvPolynomial (Fin 2) ℚ) (hl : l∈ProjectiveJLine318.grading ℚ 1)
local notation "A" => ContactOriginalLinearOpenChart318.ring c l hl
local notation "j" => ContactOriginalLinearOpenChart318.affineInto c l hl
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
abbrev curve := RelativeOriginalAffineChart318.family (CommRingCat.of ℚ) S p
abbrev projection : curve S c ⟶ Spec S := pullback.snd p (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S)
/-- The literal original affine source chart after arbitrary coefficient
change, in the SAME p-first whole original projective family. -/
abbrev into : Spec (CommRingCat.of (S ⊗[ℚ] A)) ⟶ curve S c :=
  RelativeOriginalAffineChart318.into (CommRingCat.of ℚ) S A p j
    (ContactOriginalLinearOpenChart318.affine_over c l hl)
instance openImmersion : IsOpenImmersion (into S c l hl) := inferInstance
@[reassoc] lemma over_test : into S c l hl ≫ projection S c=
    VaryingSourceCoefficientPullback318.projection ℚ A S :=
  RelativeOriginalAffineChart318.over_test (CommRingCat.of ℚ) S A p j
    (ContactOriginalLinearOpenChart318.affine_over c l hl)
instance separated : IsSeparated (projection S c) := by
  letI : IsProper p := (ContactGlobalProper318.proper_integral_extension c).2.2
  infer_instance
end ContactRelativeLinearOpenChart318
