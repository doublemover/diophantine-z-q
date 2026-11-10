module
public import IntegralUnitPairNorm318
public section
noncomputable section
namespace IntegralOriginalChartNorms318
open IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The SAME J² finite-chart coefficients of the original global pair are
primitive under every integral chart evaluation. -/
theorem branch_max (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (i : Fin 4) (φ : IntegralBranchCoordinates318.B R c i →+* K)
    (hφ : ∀ a, v (φ a)≤1) :
    max (v (φ (branchCoefficient R c i 0))) (v (φ (branchCoefficient R c i 1)))=1 :=
  IntegralUnitPairNorm318.pair_max φ v hφ _ _
    (Or.inl (IntegralScaledCoefficientUnits318.branch_zero_unit R c hN i))

/-- The original infinity frame uses its second coefficient as a unit;
the reciprocal coordinate may vanish and is never inverted here. -/
theorem infinity_max (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (φ : IntegralInfinityChart318.Order R c →+* K) (hφ : ∀ a, v (φ a)≤1) :
    max (v (φ (infinityCoefficient R c 0))) (v (φ (infinityCoefficient R c 1)))=1 :=
  IntegralUnitPairNorm318.pair_max φ v hφ _ _
    (Or.inr (IntegralScaledCoefficientUnits318.infinity_one_unit R c hN))

/-- Exact finite-frame scaling of the original pair, not a freely chosen
replacement pair having only the same projective ratio. -/
theorem branch_scaled (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (i : Fin 4) (φ : IntegralBranchCoordinates318.B R c i →+* K)
    (hφ : ∀ a, v (φ a)≤1) (α : K) :
    max (v (α*φ (branchCoefficient R c i 0))) (v (α*φ (branchCoefficient R c i 1)))=v α :=
  IntegralUnitPairNorm318.scaled_pair_max φ v hφ _ _
    (Or.inl (IntegralScaledCoefficientUnits318.branch_zero_unit R c hN i)) α

theorem infinity_scaled (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (φ : IntegralInfinityChart318.Order R c →+* K) (hφ : ∀ a, v (φ a)≤1) (α : K) :
    max (v (α*φ (infinityCoefficient R c 0))) (v (α*φ (infinityCoefficient R c 1)))=v α :=
  IntegralUnitPairNorm318.scaled_pair_max φ v hφ _ _
    (Or.inr (IntegralScaledCoefficientUnits318.infinity_one_unit R c hN)) α
end IntegralOriginalChartNorms318
