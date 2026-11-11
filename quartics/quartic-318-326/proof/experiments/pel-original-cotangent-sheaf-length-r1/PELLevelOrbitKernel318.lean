module
public import PELUnlevelledComplexBase318
public import PELEffectivePositiveLevel318
public section
noncomputable section
namespace PELLevelOrbitKernel318
open QuaternionicJointPeriodTopology318 QuaternionicUnitPeriodTransport318 QuaternionicMobiusPeriods318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELJointNormOneAction318 PELNormOneBaseAction318 PELPrincipalThreeFreeAction318
open PELPrincipalThreeCovering318 PELEffectivePositiveLevel318
set_option maxHeartbeats 1600000

@[expose] def principalEmbedding : principalThree →* normOneUnits where
  toFun u := ⟨u.val,u.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem principal_reduces (u : principalThree) : effectiveReduction (principalEmbedding u)=1 :=
  (effective_kernel_congruence _).mpr (Or.inl u.property.2)

theorem signs_reduce (u : normOneUnits) (hu : u.val=1 ∨ u.val= -1) : effectiveReduction u=1 := by
  apply (effective_kernel_congruence u).mpr
  rcases hu with h | h
  · left
    refine ⟨0,?_⟩
    rw [h]
    simp
  · right
    refine ⟨0,?_⟩
    rw [h]
    simp

@[expose] def negative (u : normOneUnits) : normOneUnits :=
  ⟨-u.val,(mem_normOneUnits _).mpr (by
    change reducedNorm (-((u.val:order):B))=1
    simpa [reducedNorm] using (mem_normOneUnits u.val).mp u.property)⟩

theorem negative_action (u : normOneUnits) (τ : HalfPlane) : negative u • τ=u • τ := by
  apply Subtype.ext
  change mobius (representation (-((u.val:order):B))) τ=
    mobius (representation ((u.val:order):B)) τ
  rw [map_neg]
  simp only [mobius,denominator,Matrix.neg_apply,Complex.ofReal_neg,neg_mul,←neg_add,neg_div_neg]

/-- The stabilizer of EVERY fine-level base orbit is precisely the actual
effective finite-level kernel. This uses both the original ±1 stabilizer and
the exact original-order congruence criterion. -/
theorem fixes_fine_iff (u : normOneUnits) (τ : HalfPlane) :
    baseQuotient (u • τ)=baseQuotient τ ↔ effectiveReduction u=1 := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := base_covering.apply_eq_iff_mem_orbit.mp h
    let w : normOneUnits := u⁻¹*principalEmbedding k
    have hw : w • τ=τ := by
      change (u⁻¹*principalEmbedding k) • τ=τ
      rw [mul_smul]
      change u⁻¹ • (k • τ)=τ
      rw [hk,smul_smul,inv_mul_cancel,one_smul]
    have hr := signs_reduce w (stabilizer_sign w τ hw)
    have hi : (effectiveReduction u)⁻¹=1 := by
      simpa only [w,map_mul,map_inv,principal_reduces,mul_one] using hr
    exact inv_eq_one.mp hi
  · intro h
    rcases (effective_kernel_congruence u).mp h with ⟨v,hv⟩ | ⟨v,hv⟩
    · let k : principalThree := ⟨u.val,u.property,⟨v,hv⟩⟩
      change baseQuotient (k • τ)=baseQuotient τ
      exact base_covering.map_smul k
    · have hn : ((negative u).val:order)=1+(3:ℕ) • (-v) := by
        change -(u.val:order)=1+(3:ℕ) • (-v)
        rw [hv]
        simp only [nsmul_neg]
        abel
      let k : principalThree := ⟨(negative u).val,(negative u).property,⟨-v,hn⟩⟩
      calc
        baseQuotient (u • τ)=baseQuotient (negative u • τ) :=
          congrArg baseQuotient (negative_action u τ).symm
        _ = baseQuotient τ := base_covering.map_smul k

theorem orbit_eq_iff (u v : normOneUnits) (τ : HalfPlane) :
    baseQuotient (u • τ)=baseQuotient (v • τ) ↔ effectiveReduction u=effectiveReduction v := by
  have ha : (u*v⁻¹) • (v • τ)=u • τ := by
    rw [smul_smul,mul_assoc,inv_mul_cancel,mul_one]
  have h := fixes_fine_iff (u*v⁻¹) (v • τ)
  rw [ha,map_mul,map_inv,mul_inv_eq_one] at h
  exact h
end PELLevelOrbitKernel318
