module
public import ContactFinitePlaceBaseMap318
public section
noncomputable section
namespace FinitePlaceChartPairBounds318
open NumberField ActualFinitePlaceIntegers318 ContactFinitePlaceBaseMap318
open ContactArithmeticDenominator318 IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type*} [Field K] [NumberField K]
variable (c : Fin 4 → ℚˣ) (v : FinitePlace K) (hv : v (denominator c:K)=1)

/-- The finite-place norm bound is DERIVED for a genuine integral branch
center. The coefficients are the original J² pair with the exact transported
original twists; no caller integrality inequalities are required. -/
theorem branch_bound (i : Fin 4)
    (φ : IntegralBranchCoordinates318.B (Integers v) (twists c v hv) i →+* Integers v)
    (α a0 a1 : K) (hα : α≠0)
    (ha0 : a0=α*algebraMap (Integers v) K
      (φ (branchCoefficient (Integers v) (twists c v hv) i 0)))
    (ha1 : a1=α*algebraMap (Integers v) K
      (φ (branchCoefficient (Integers v) (twists c v hv) i 1))) :
    (∀ n : Fin 2, v (![a0,a1] n)*(v α)⁻¹≤1) ∧
      max (v a0) (v a1)=v α :=
  IntegralChartFrameBounds318.branch_bound (Integers v) (twists c v hv)
    (separation_unit c v hv) v i ((algebraMap (Integers v) K).comp φ)
    (center_bound v φ) α a0 a1 hα ha0 ha1

/-- The same actual-place result on the original whole infinity chart,
including centers with zero reciprocal coordinate. -/
theorem infinity_bound
    (φ : IntegralInfinityChart318.Order (Integers v) (twists c v hv) →+* Integers v)
    (α a0 a1 : K) (hα : α≠0)
    (ha0 : a0=α*algebraMap (Integers v) K
      (φ (infinityCoefficient (Integers v) (twists c v hv) 0)))
    (ha1 : a1=α*algebraMap (Integers v) K
      (φ (infinityCoefficient (Integers v) (twists c v hv) 1))) :
    (∀ n : Fin 2, v (![a0,a1] n)*(v α)⁻¹≤1) ∧
      max (v a0) (v a1)=v α :=
  IntegralChartFrameBounds318.infinity_bound (Integers v) (twists c v hv)
    (separation_unit c v hv) v ((algebraMap (Integers v) K).comp φ)
    (center_bound v φ) α a0 a1 hα ha0 ha1
end FinitePlaceChartPairBounds318
