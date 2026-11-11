module
public import ContactGlobalProper318
public import ContactIntrinsicDifferentials318
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace ContactOriginalLinearOpenChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable (c : Fin 4 → ℚˣ) (l : MvPolynomial (Fin 2) ℚ)
  (hl : l∈ProjectiveJLine318.grading ℚ 1)
/-- The literal affine homogeneous-localization chart, without replacing
its ring by an assumed polynomial-coordinate model. -/
abbrev baseRing := Away (ProjectiveJLine318.grading ℚ) l
abbrev baseInto : Spec (CommRingCat.of (baseRing l)) ⟶ ProjectiveJLine318.scheme ℚ :=
  Proj.awayι (ProjectiveJLine318.grading ℚ) l hl (by omega)
abbrev chart := pullback (ContactProjectiveModel318.modelMap c) (baseInto l hl)
abbrev into : chart c l hl ⟶ ContactProjectiveModel318.model c :=
  pullback.fst (ContactProjectiveModel318.modelMap c) (baseInto l hl)
abbrev toBase : chart c l hl ⟶ Spec (CommRingCat.of (baseRing l)) :=
  pullback.snd (ContactProjectiveModel318.modelMap c) (baseInto l hl)
instance openImmersion : IsOpenImmersion (into c l hl) := inferInstance
instance finite : IsFinite (toBase c l hl) := by
  letI := ContactGlobalProper318.normalization_finite c
  infer_instance
instance affine : IsAffine (chart c l hl) := isAffine_of_isAffineHom (toBase c l hl)
/-- This is an actual affine open of the SAME original projective model. -/
lemma cartesian : IsPullback (into c l hl) (toBase c l hl)
    (ContactProjectiveModel318.modelMap c) (baseInto l hl) :=
  IsPullback.of_hasPullback _ _
abbrev ring : CommRingCat := Γ(chart c l hl,⊤)
@[expose] def coefficient : CommRingCat.of ℚ ⟶ ring c l hl :=
  Spec.preimage ((chart c l hl).isoSpec.inv ≫ into c l hl ≫ ContactIntrinsicDifferentials318.structureMap c)
@[expose] instance algebra : Algebra ℚ (ring c l hl) := (coefficient c l hl).hom.toAlgebra
@[expose] def affineInto : Spec (ring c l hl) ⟶ ContactProjectiveModel318.model c :=
  (chart c l hl).isoSpec.inv ≫ into c l hl
instance affine_open : IsOpenImmersion (affineInto c l hl) := by unfold affineInto; infer_instance
@[reassoc] lemma affine_over : affineInto c l hl ≫ ContactIntrinsicDifferentials318.structureMap c=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (ring c l hl))) := by
  change ((chart c l hl).isoSpec.inv ≫ into c l hl) ≫ ContactIntrinsicDifferentials318.structureMap c=
    Spec.map (coefficient c l hl)
  rw [coefficient,Spec.map_preimage,Category.assoc]
/-- An arbitrary rational fiber complement, supplied as an actual
homogeneous linear form on the original projective contact line. -/
@[expose] def linearForm (a : ℚ) : MvPolynomial (Fin 2) ℚ := X 0-a • X 1
lemma linearForm_homogeneous (a : ℚ) : linearForm a∈ProjectiveJLine318.grading ℚ 1 :=
  (ProjectiveJLine318.grading ℚ 1).sub_mem (isHomogeneous_X ℚ 0)
    ((ProjectiveJLine318.grading ℚ 1).smul_mem a (isHomogeneous_X ℚ 1))
end ContactOriginalLinearOpenChart318
