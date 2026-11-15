module
public import PELActualPrincipalThreeQuotient318
public section
noncomputable section
namespace PELEffectivePositiveLevel318
open PELOrderReductionThree318 PELFiniteNormOneGroup318 PELActualPrincipalThreeQuotient318
set_option maxHeartbeats 1200000

/-- The actual central minus-one element belongs to the finite norm-one
group because the same quadratic reduced norm sends scalar minus one to one. -/
@[expose] def minusOne : normOne := ⟨-1,by
  apply (mem_normOne _).mpr
  change QuadraticAlgebra.norm (PELActualLevelThreeQuotient318.quotientResidue (-1))=1
  rw [map_neg,map_one]
  norm_num [QuadraticAlgebra.norm_def]⟩
@[expose] def signs : Subgroup normOne := Subgroup.zpowers minusOne

theorem minusOne_mul : minusOne*minusOne=1 := by
  apply Subtype.ext
  apply Units.ext
  change (-1:QuotientOrder)*(-1:QuotientOrder)=1
  simp

theorem minusOne_inv : minusOne⁻¹=minusOne := by
  calc
    minusOne⁻¹=minusOne⁻¹*1 := (mul_one _).symm
    _ = minusOne⁻¹*(minusOne*minusOne) := congrArg (fun z : normOne => minusOne⁻¹*z) minusOne_mul.symm
    _ = minusOne := by rw [←mul_assoc,inv_mul_cancel,one_mul]

@[expose] def signPair : Subgroup normOne where
  carrier := {u | u=1 ∨ u=minusOne}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl|rfl) (rfl|rfl) <;> simp [minusOne_mul]
  inv_mem' := by
    rintro a (rfl|rfl)
    · exact Or.inl (inv_one)
    · exact Or.inr minusOne_inv

theorem signs_eq_pair : signs=signPair := by
  apply le_antisymm
  · apply Subgroup.zpowers_le.mpr
    exact Or.inr rfl
  · intro u hu
    rcases hu with rfl|rfl
    · exact signs.one_mem
    · exact Subgroup.mem_zpowers minusOne

theorem signs_membership (u : normOne) : u∈signs ↔ u=1 ∨ u=minusOne := by
  rw [signs_eq_pair]
  rfl

instance signs_normal : signs.Normal := by
  apply Subgroup.normal_of_le_center
  rw [signs,Subgroup.zpowers_le,Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  apply Units.ext
  change (-1:QuotientOrder)*(u.val:QuotientOrder)=(u.val:QuotientOrder)*(-1:QuotientOrder)
  simp

theorem signs_card : Nat.card signs=2 := by
  rw [signs,Nat.card_zpowers]
  apply orderOf_eq_prime (p:=2)
  · apply Subtype.ext
    apply Units.ext
    change (-1:QuotientOrder)^2=1
    simp
  · intro h
    have hv : (-1:QuotientOrder)=1 :=
      congrArg (fun u : normOne => (u.val:QuotientOrder)) h
    apply PELActualLevelThreeQuotient318.quotient_two_ne_zero
    calc
      (2:QuotientOrder)=1+1 := by norm_num
      _ = (-1:QuotientOrder)+1 := by rw [hv]
      _ = 0 := by simp

abbrev EffectivePositiveLevel := normOne ⧸ signs

theorem effective_level_card : Nat.card EffectivePositiveLevel=18 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup signs
  rw [normOne_card,signs_card] at h
  omega

@[expose] def effectiveReduction : PELJointNormOneAction318.normOneUnits →* EffectivePositiveLevel :=
  (QuotientGroup.mk' signs).comp normOneReduction

theorem effectiveReduction_surjective : Function.Surjective effectiveReduction := by
  intro x
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective signs x
  obtain ⟨v,rfl⟩ := normOneReduction_surjective u
  exact ⟨v,rfl⟩

/-- Quotienting the actual positive arithmetic group by its exact effective
level kernel gives18, not the whole adelic/component-inclusive36. -/
@[expose] def effectiveQuotientEquiv :
    PELJointNormOneAction318.normOneUnits ⧸ effectiveReduction.ker ≃* EffectivePositiveLevel :=
  QuotientGroup.quotientKerEquivOfSurjective effectiveReduction effectiveReduction_surjective

theorem original_effective_card :
    Nat.card (PELJointNormOneAction318.normOneUnits ⧸ effectiveReduction.ker)=18 := by
  rw [Nat.card_congr effectiveQuotientEquiv.toEquiv]
  exact effective_level_card

/-- Exact effective kernel: the original global unit is congruent to one
of the TWO central scalars in the original order, with no enlarged level. -/
theorem effective_kernel_congruence (u : PELJointNormOneAction318.normOneUnits) :
    u∈effectiveReduction.ker ↔
      (∃ v : PELPrincipalOrderCoordinates318.order,(u.val:PELPrincipalOrderCoordinates318.order)=1+(3:ℕ) • v) ∨
      (∃ v : PELPrincipalOrderCoordinates318.order,(u.val:PELPrincipalOrderCoordinates318.order)= -1+(3:ℕ) • v) := by
  change (QuotientGroup.mk (normOneReduction u):EffectivePositiveLevel)=1 ↔ _
  rw [QuotientGroup.eq_one_iff,signs_membership]
  have hpos : normOneReduction u=1 ↔ PELGlobalUnitReductionSurjective318.originalUnitReduction u.val=1 :=
    ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  have hneg : normOneReduction u=minusOne ↔ PELGlobalUnitReductionSurjective318.originalUnitReduction u.val= -1 :=
    ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  rw [hpos,hneg,PELOriginalCongruenceKernel318.reduction_one_iff,
    PELOriginalCongruenceKernel318.reduction_minus_one_iff]
end PELEffectivePositiveLevel318
