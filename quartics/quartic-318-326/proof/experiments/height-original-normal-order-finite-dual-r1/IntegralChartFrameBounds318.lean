module
public import IntegralOriginalChartNorms318
public section
noncomputable section
namespace IntegralChartFrameBounds318
open NumberField IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
variable {K : Type*} [Field K] [NumberField K]

/-- Once an actual finite branch center and its actual rational-frame
comparison are supplied, the ORIGINAL evaluated section pair satisfies the
finite-place bound with the exact integral-frame norm. -/
theorem branch_bound (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (v : FinitePlace K) (i : Fin 4) (φ : IntegralBranchCoordinates318.B R c i →+* K)
    (hφ : ∀ a, v (φ a)≤1) (α a0 a1 : K) (hα : α≠0)
    (ha0 : a0=α*φ (branchCoefficient R c i 0))
    (ha1 : a1=α*φ (branchCoefficient R c i 1)) :
    (∀ n : Fin 2, v (![a0,a1] n)*(v α)⁻¹≤1) ∧
      max (v a0) (v a1)=v α := by
  subst a0 a1
  have h := IntegralUnitPairNorm318.normalized_pair_bound φ v.val hφ _ _
    (Or.inl (IntegralScaledCoefficientUnits318.branch_zero_unit R c hN i)) α hα
  refine ⟨?_,IntegralOriginalChartNorms318.branch_scaled R c v.val hN i φ hφ α⟩
  intro n
  fin_cases n
  · exact h.1
  · exact h.2

/-- The same result at the original infinity center, without inverting its
zero reciprocal coordinate or replacing its second generating coefficient. -/
theorem infinity_bound (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (v : FinitePlace K) (φ : IntegralInfinityChart318.Order R c →+* K)
    (hφ : ∀ a, v (φ a)≤1) (α a0 a1 : K) (hα : α≠0)
    (ha0 : a0=α*φ (infinityCoefficient R c 0))
    (ha1 : a1=α*φ (infinityCoefficient R c 1)) :
    (∀ n : Fin 2, v (![a0,a1] n)*(v α)⁻¹≤1) ∧
      max (v a0) (v a1)=v α := by
  subst a0 a1
  have h := IntegralUnitPairNorm318.normalized_pair_bound φ v.val hφ _ _
    (Or.inr (IntegralScaledCoefficientUnits318.infinity_one_unit R c hN)) α hα
  refine ⟨?_,IntegralOriginalChartNorms318.infinity_scaled R c v.val hN φ hφ α⟩
  intro n
  fin_cases n
  · exact h.1
  · exact h.2

/-- Different actual integral centers/frames give the same local frame
norm when they represent the same original section values. -/
theorem frame_norm_unique (v : FinitePlace K) (a0 a1 α β : K)
    (hα : max (v a0) (v a1)=v α) (hβ : max (v a0) (v a1)=v β) :
    (v α)⁻¹=(v β)⁻¹ := congrArg Inv.inv (hα.symm.trans hβ)
end IntegralChartFrameBounds318
