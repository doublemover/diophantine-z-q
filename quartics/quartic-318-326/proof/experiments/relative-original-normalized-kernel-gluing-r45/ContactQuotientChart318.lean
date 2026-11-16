module
public import ContactAffineQuotientToProjective318
public import AffineWholeFamilyNaturality318
public import ClosedImmersionOpenLift318
public section
noncomputable section
namespace ContactQuotientChart318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
/-- An actual homogeneous linear-form affine chart of the ORIGINAL
normalization, with its original rational structure. -/
structure Chart where
  form : MvPolynomial (Fin 2) ℚ
  homogeneous : form∈ProjectiveJLine318.grading ℚ 1
variable (c : Fin 4 → ℚˣ) (a : Chart)
abbrev ring := ContactOriginalLinearOpenChart318.ring c a.form a.homogeneous
abbrev original : Spec (ring c a) ⟶ ContactProjectiveModel318.model c :=
  ContactOriginalLinearOpenChart318.affineInto c a.form a.homogeneous
variable (S : CommRingCat.{0}) [Algebra ℚ S]
abbrev into := ContactRelativeLinearOpenChart318.into S c a.form a.homogeneous
abbrev Ideal (n : ℕ) := VaryingProjectiveQuotientEquiv318.ProjectiveIdeal ℚ (ring c a) (Fin n) S
variable (n : ℕ) (I : Ideal c a S n)
abbrev family := VaryingWholeIdealFamily318.family ℚ (ring c a) S I.val
abbrev quotientInto := VaryingWholeIdealFamily318.into ℚ (ring c a) S I.val
abbrev projectiveInto := ContactAffineQuotientToProjective318.into S c a.form a.homogeneous n I
abbrev projection := VaryingWholeIdealFamily318.projection ℚ (ring c a) S I.val
instance presentation : LocallyOfFinitePresentation (projection c a S n I) :=
  VaryingLocalFreeFamilyPresentation318.presentation ℚ (ring c a) (Fin n) S
    (VaryingProjectiveQuotientEquiv318.toLocal ℚ (ring c a) (Fin n) S I)
lemma rank (x : PrimeSpectrum S) : (projection c a S n I).finrank x=Fintype.card (Fin n) := by
  letI := I.property.1
  letI := I.property.2.1
  have h : Spec.map (CommRingCat.ofHom (algebraMap S ((S ⊗[ℚ] ring c a) ⧸ I.val)))=
      projection c a S n I := by
    change Spec.map (CommRingCat.ofHom (algebraMap S ((S ⊗[ℚ] ring c a) ⧸ I.val)))=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.val)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[ℚ] ring c a)))
    rw [← Spec.map_comp]
    rfl
  rw [← h,Scheme.Hom.finrank_SpecMap_algebraMap]
  exact I.property.2.2 x
end ContactQuotientChart318
