module
public import PELOriginalPolarizedOrderAction318
public section
noncomputable section
namespace PELOriginalOrderIntegralNorm318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 QuaternionAlgebra
/-- Standard quaternion conjugation, distinct from the positive Rosati
involution, preserved on the EXACT original half-integral order. -/
@[expose] def conjugateCoordinates (x : Coordinates) : Coordinates :=
  ![x 0+x 2,-x 1,-x 2,-x 3]
@[expose] def conjugate (a : order) : order :=
  coordinatesEquiv (conjugateCoordinates (coordinatesEquiv.symm a))
lemma conjugate_value (a : order) : (conjugate a:B)=star (a:B) := by
  obtain ⟨x,rfl⟩ := coordinatesEquiv.surjective a
  simp only [conjugate,AddEquiv.symm_apply_apply,coordinatesEquiv_value]
  ext <;> simp [conjugateCoordinates,embed] <;> ring
@[expose] def normCoordinates (x : Coordinates) : ℤ :=
  x 0^2+x 0*x 2-x 2^2+210*x 1^2+210*x 1*x 3+42*x 3^2
@[expose] def norm (a : order) : ℤ := normCoordinates (coordinatesEquiv.symm a)
lemma norm_value (a : order) : (norm a:ℚ)=reducedNorm (a:B) := by
  obtain ⟨x,rfl⟩ := coordinatesEquiv.surjective a
  simp only [norm,AddEquiv.symm_apply_apply,coordinatesEquiv_value]
  simp [normCoordinates,reducedNorm,embed]
  <;> push_cast <;> ring
/-- The original integer norm, not the positive Hermitian weight, is
what both actual conjugate composites represent. -/
lemma mul_conjugate (a : order) : a*conjugate a=(norm a:order) := by
  apply Subtype.ext
  change (a:B)*(conjugate a:B)=(norm a:B)
  rw [conjugate_value,norm_identity,←norm_value]
  simp only [map_intCast]
lemma conjugate_mul (a : order) : conjugate a*a=(norm a:order) := by
  apply Subtype.ext
  change (conjugate a:B)*(a:B)=(norm a:B)
  rw [conjugate_value]
  have he : star (a:B)*(a:B)=(a:B)*star (a:B) := by
    ext <;> simp <;> ring
  rw [he,norm_identity,←norm_value]
  simp only [map_intCast]
end PELOriginalOrderIntegralNorm318
