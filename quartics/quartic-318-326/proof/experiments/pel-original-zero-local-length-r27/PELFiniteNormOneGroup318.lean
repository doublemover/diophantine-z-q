module
public import PELGlobalNormOneLevelLifts318
public section
noncomputable section
namespace PELFiniteNormOneGroup318
open PELOrderReductionThree318 PELActualLevelThreeQuotient318
open PELGlobalIntegralUnitLifts318 PELGlobalUnitReductionSurjective318
set_option maxHeartbeats 1200000

@[expose] def ringNorm : QuotientOrder →* F3 :=
  QuadraticAlgebra.norm.comp quotientResidue.toMonoidHom
@[expose] def unitNorm : QuotientOrderˣ →* F3ˣ := Units.map ringNorm
@[expose] def normOne : Subgroup QuotientOrderˣ := unitNorm.ker

theorem mem_normOne (u : QuotientOrderˣ) :
    u∈normOne ↔ PELLevelThreeSimilitudes318.norm (u:QuotientOrder)=1 := by
  change unitNorm u=1 ↔ _
  constructor
  · intro h
    exact congrArg (fun z : F3ˣ => (z:F3)) h
  · intro h
    apply Units.ext
    exact h

theorem residue_units (u : F3ˣ) : u=1 ∨ u= -1 := by
  have hne := u.ne_zero
  have hv : (u:F3)=1 ∨ (u:F3)= -1 := by
    generalize h : (u:F3)=x at hne ⊢
    fin_cases x <;> norm_num at hne ⊢
  rcases hv with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

@[expose] def twoUnits (i : Fin 2) : F3ˣ := if i=0 then 1 else -1

theorem twoUnits_bijective : Function.Bijective twoUnits := by
  constructor
  · intro i j h
    have hv := congrArg (fun u : F3ˣ => (u:F3)) h
    fin_cases i <;> fin_cases j <;> norm_num [twoUnits] at hv ⊢
  · intro u
    rcases residue_units u with h | h
    · exact ⟨0,by simp [twoUnits,h]⟩
    · exact ⟨1,by simp [twoUnits,h]⟩

theorem scalar_units_card : Nat.card F3ˣ=2 := by
  rw [←Nat.card_congr (Equiv.ofBijective twoUnits twoUnits_bijective)]
  simp

theorem generator_norm_image : unitNorm (originalUnitReduction (generator 0))= -1 := by
  apply Units.ext
  change QuadraticAlgebra.norm
    (PELReductionResidueField318.residue (reduction (generator 0:PELPrincipalOrderCoordinates318.order)))= -1
  rw [generator_reduction]
  norm_num [finiteGenerator,PELReductionResidueField318.residue,QuadraticAlgebra.norm_def]

theorem unitNorm_surjective : Function.Surjective unitNorm := by
  intro u
  rcases residue_units u with h | h
  · exact ⟨1,(map_one unitNorm).trans h.symm⟩
  · exact ⟨originalUnitReduction (generator 0),generator_norm_image.trans h.symm⟩

/-- The actual finite norm-one group has36 elements, while the full unit
group has72. This uses the genuine surjective norm map, not a guessed half. -/
theorem normOne_card : Nat.card normOne=36 := by
  have h := Subgroup.card_ker_mul_card_of_surjective unitNorm_surjective
  change Nat.card normOne * Nat.card F3ˣ=Nat.card QuotientOrderˣ at h
  rw [scalar_units_card,actual_counts.2.2.1] at h
  omega
end PELFiniteNormOneGroup318
