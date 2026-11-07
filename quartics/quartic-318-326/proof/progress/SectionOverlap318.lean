module
public import AffineSectionExtension318
public section
noncomputable section
namespace SectionOverlap318
open VerticalSection318
set_option maxHeartbeats 0
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- Genuine rescaling of the relative derivation gives the quadratic frame law. -/
theorem section0_smul (D : Derivation R K K) (u t : K) :
    section0 (u • D) t = u^2 * section0 D t := by
  simp only [section0,Derivation.smul_apply,smul_eq_mul]
  ring

theorem section1_smul (D : Derivation R K K) (u t : K) :
    section1 (u • D) t = u^2 * section1 D t := by
  rw [section1,section0_smul,section1]
  ring

variable {C : Type*} [CommRing C]

/-- The actual invertible linear transition of a pair of quadratic coefficients. -/
noncomputable def frameChange (u : Cˣ) : (C × C) ≃ₗ[C] (C × C) :=
  LinearEquiv.smulOfUnit (u^2)

theorem frameChange_apply (u : Cˣ) (a : C × C) :
    frameChange u a = ((u:C)^2*a.1,(u:C)^2*a.2) := by
  rfl

theorem frameChange_one (a : C × C) : frameChange 1 a = a := by
  simp [frameChange_apply]

theorem frameChange_comp (u v : Cˣ) (a : C × C) :
    frameChange u (frameChange v a) = frameChange (u*v) a := by
  simp only [frameChange_apply,Units.val_mul]
  apply Prod.ext <;> simp only [Prod.fst,Prod.snd] <;> ring

theorem frameChange_inverse (u : Cˣ) (a : C × C) :
    frameChange (u⁻¹) (frameChange u a) = a := by
  rw [frameChange_comp,inv_mul_cancel,frameChange_one]

section Overlap
variable {A : Type*} [CommRing A] [IsDomain C] [Algebra A C]
  [Algebra C K] [Algebra A K] [IsScalarTower A C K] [IsFractionRing C K]

/-- Uniqueness in the actual overlap fraction field identifies independently
extended affine coefficients with the exact quadratic transition. -/
theorem overlap_pair (D : Derivation R K K) (t : K) (u : Cˣ)
    (a : A × A) (b : C × C)
    (ha0 : algebraMap A K a.1 = section0 D t)
    (ha1 : algebraMap A K a.2 = section1 D t)
    (hb0 : algebraMap C K b.1 = section0 ((algebraMap C K (u:C)) • D) t)
    (hb1 : algebraMap C K b.2 = section1 ((algebraMap C K (u:C)) • D) t) :
    b = frameChange u (algebraMap A C a.1, algebraMap A C a.2) := by
  rw [frameChange_apply]
  apply Prod.ext
  · apply IsFractionRing.injective C K
    rw [map_mul,map_pow,←IsScalarTower.algebraMap_apply A C K a.1,ha0,hb0,section0_smul]
  · apply IsFractionRing.injective C K
    rw [map_mul,map_pow,←IsScalarTower.algebraMap_apply A C K a.2,ha1,hb1,section1_smul]

end Overlap
end SectionOverlap318
