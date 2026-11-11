module
public import PELFiniteNormOneGroup318
public import PELPrincipalThreeFreeAction318
public section
noncomputable section
namespace PELOriginalCongruenceKernel318
open PELOrderReductionThree318 PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318
open PELGlobalUnitReductionSurjective318 PELJointNormOneAction318
open PELPrincipalThreeFreeAction318
set_option maxHeartbeats 1200000

/-- The actual unit reduction kernel is exactly the original principal
congruence condition used by the holomorphic family action. -/
theorem reduction_one_iff (u : orderˣ) :
    originalUnitReduction u=1 ↔ ∃ v : order,(u:order)=1+(3:ℕ) • v := by
  have hq : originalUnitReduction u=1 ↔ reduction (u:order)=1 := by
    constructor
    · intro h
      have hh := congrArg (fun z : QuotientOrderˣ => quotientEquiv (z:QuotientOrder)) h
      simpa only [map_one] using hh
    · intro h
      apply Units.ext
      apply quotientEquiv.injective
      change reduction (u:order)=quotientEquiv 1
      rw [map_one]
      exact h
  rw [hq]
  constructor
  · intro h
    have hz : reduction ((u:order)-1)=0 := by rw [map_sub,h,map_one,sub_self]
    obtain ⟨v,hv⟩ := (kernel_iff_three ((u:order)-1)).mp hz
    refine ⟨v,?_⟩
    have he : (u:order)-1=(3:ℕ) • v := by simpa only [nsmul_eq_mul,zsmul_eq_mul,Int.cast_ofNat] using hv
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  · rintro ⟨v,hv⟩
    rw [hv,map_add,map_one,map_nsmul]
    simp only [nsmul_eq_mul]
    norm_num

theorem reduction_one_iff_congruent (u : orderˣ) :
    originalUnitReduction u=1 ↔ u∈congruentOneThree := reduction_one_iff u

/-- Norm-one global units reduce into the SAME finite reduced-norm-one group. -/
theorem norm_one_reduces (u : orderˣ) (hu : reducedNorm ((u:order):B)=1) :
    PELLevelThreeSimilitudes318.norm (originalUnitReduction u:QuotientOrder)=1 := by
  obtain ⟨a,ha⟩ := coordinatesEquiv.surjective (u:order)
  have hn : PELLevelThreeSimilitudes318.integralNorm a=1 := by
    have hq : (PELLevelThreeSimilitudes318.integralNorm a:ℚ)=1 := by
      rw [←PELLevelThreeSimilitudes318.original_norm]
      have he : embed a=((u:order):B) := congrArg order.subtype ha
      rw [he]
      exact hu
    exact_mod_cast hq
  change PELLevelThreeSimilitudes318.norm (moduloThree.mk' (u:order))=1
  rw [←ha,PELLevelThreeSimilitudes318.norm_original,hn]
  norm_num

/-- The second effective scalar class is literal minus one modulo3O. -/
theorem reduction_minus_one_iff (u : orderˣ) :
    originalUnitReduction u= -1 ↔ ∃ v : order,(u:order)= -1+(3:ℕ) • v := by
  have hq : originalUnitReduction u= -1 ↔ reduction (u:order)= -1 := by
    constructor
    · intro h
      have hh := congrArg (fun z : QuotientOrderˣ => quotientEquiv (z:QuotientOrder)) h
      simpa only [map_neg,map_one] using hh
    · intro h
      apply Units.ext
      apply quotientEquiv.injective
      change reduction (u:order)=quotientEquiv (-1)
      rw [map_neg,map_one]
      exact h
  rw [hq]
  constructor
  · intro h
    have hz : reduction ((u:order)+1)=0 := by rw [map_add,h,map_one,neg_add_cancel]
    obtain ⟨v,hv⟩ := (kernel_iff_three ((u:order)+1)).mp hz
    refine ⟨v,?_⟩
    have he : (u:order)+1=(3:ℕ) • v := by
      simpa only [nsmul_eq_mul,zsmul_eq_mul,Int.cast_ofNat] using hv
    calc
      (u:order)=((u:order)+1)-1 := by abel
      _ = (3:ℕ) • v-1 := congrArg (fun z : order => z-1) he
      _ = -1+(3:ℕ) • v := by abel
  · rintro ⟨v,hv⟩
    rw [hv,map_add,map_neg,map_one,map_nsmul]
    simp only [nsmul_eq_mul]
    norm_num
end PELOriginalCongruenceKernel318
