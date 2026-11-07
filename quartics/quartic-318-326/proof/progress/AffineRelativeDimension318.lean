module
public import OpenJAffineScheme318
public section
noncomputable section
namespace AffineRelativeDimension318
open Algebra AlgebraicGeometry ShortAffineJacobian318
set_option maxHeartbeats 0
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual localized two-variable one-relation presentation has relative dimension one. -/
theorem localization_dimension_one (P : PreSubmersivePresentation R S (Fin 2) Unit) :
    IsStandardSmoothOfRelativeDimension 1 R (Localization.Away P.jacobian) := by
  let T := Localization.Away P.jacobian
  let Q : PreSubmersivePresentation S T Unit Unit :=
    PreSubmersivePresentation.localizationAway T P.jacobian
  let E : SubmersivePresentation R T (Unit ⊕ Fin 2) (Unit ⊕ Unit) :=
    { toPreSubmersivePresentation := Q.comp P
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,Algebra.smul_def]
        have hu := IsLocalization.Away.algebraMap_isUnit (S := T) P.jacobian
        apply hu.mul
        change IsUnit (PreSubmersivePresentation.localizationAway T P.jacobian).jacobian
        rw [PreSubmersivePresentation.localizationAway_jacobian]
        exact hu }
  apply E.isStandardSmoothOfRelativeDimension
  change Nat.card (Unit ⊕ Fin 2)-Nat.card (Unit ⊕ Unit)=1
  norm_num [Nat.card_sum]

/-- The actual short Weierstrass affine scheme is smooth of relative dimension one. -/
theorem structure_dimension_one (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    SmoothOfRelativeDimension 1 (ShortAffineScheme318.structureMap A B) := by
  apply HasRingHomProperty.Spec_iff.mpr
  refine ⟨Set.range (fun i : Fin 2 => (presentation A B i).jacobian),jacobian_span A B hD,?_⟩
  rintro t ⟨i,rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap (Ring A B) (Localization.Away (presentation A B i).jacobian)).comp
      (algebraMap R (Ring A B)))
  rw [← IsScalarTower.algebraMap_eq,RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact localization_dimension_one (presentation A B i)

/-- No dimension or geometric-fiber assumption remains for the literal OpenJ affine family. -/
instance literal_dimension_one (N : ℕ) :
    SmoothOfRelativeDimension 1 (OpenJAffineScheme318.structureMap N) :=
  structure_dimension_one (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
    (OpenJAffineScheme318.discriminant_unit N)

end AffineRelativeDimension318
