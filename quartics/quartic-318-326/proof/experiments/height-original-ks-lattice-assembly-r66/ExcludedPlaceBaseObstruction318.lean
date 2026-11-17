module
public import ContactFinitePlaceBaseMap318
public section
noncomputable section
namespace ExcludedPlaceBaseObstruction318
open NumberField ActualFinitePlaceIntegers318 ContactArithmeticDenominator318
variable {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)

/-- Every genuine unit of the local integer ring has absolute value one;
both the unit and its inverse satisfy the actual integer-ring bound. -/
theorem unit_norm (u : (Integers v)ˣ) :
    v (algebraMap (Integers v) K (u : Integers v)) = 1 := by
  have hp : v (algebraMap (Integers v) K (u : Integers v)) *
      v (algebraMap (Integers v) K ((u⁻¹ : (Integers v)ˣ) : Integers v)) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  apply le_antisymm (integer_bound v (u : Integers v))
  calc
    1 = v (algebraMap (Integers v) K (u : Integers v)) *
        v (algebraMap (Integers v) K ((u⁻¹ : (Integers v)ˣ) : Integers v)) := hp.symm
    _ ≤ v (algebraMap (Integers v) K (u : Integers v)) * 1 :=
      mul_le_mul_of_nonneg_left (integer_bound v ((u⁻¹ : (Integers v)ˣ) : Integers v))
        (v.nonneg _)
    _ = v (algebraMap (Integers v) K (u : Integers v)) := mul_one _

theorem isUnit_norm (a : Integers v) (ha : IsUnit a) :
    v (algebraMap (Integers v) K a) = 1 := by
  obtain ⟨u, rfl⟩ := ha
  exact unit_norm v u

variable (c : Fin 4 → ℚˣ)

/-- The denominator-unit condition is necessary for ANY unital map from the
existing localized arithmetic base to this valuation ring, not merely for the
particular lift used by the good-place construction. -/
theorem denominator_norm_of_baseMap
    (φ : ContactArithmeticBase318.Base c →+* Integers v) :
    v (denominator c : K) = 1 := by
  have hu : IsUnit (denominator c : Integers v) := by
    simpa using (ContactArithmeticBase318.denominator_unit c).map φ
  simpa using isUnit_norm v (denominator c : Integers v) hu

/-- Exact scope of the existing model's integral base change. No additional
choice of chart or embedding can make that same base work at an excluded place. -/
theorem baseMap_exists_iff :
    Nonempty (ContactArithmeticBase318.Base c →+* Integers v) ↔
      v (denominator c : K) = 1 := by
  constructor
  · rintro ⟨φ⟩
    exact denominator_norm_of_baseMap v c φ
  · intro hv
    exact ⟨ContactFinitePlaceBaseMap318.baseMap c v hv⟩

theorem no_baseMap_at_excluded (hv : v (denominator c : K) ≠ 1) :
    ¬Nonempty (ContactArithmeticBase318.Base c →+* Integers v) := by
  intro h
  exact hv ((baseMap_exists_iff v c).mp h)

end ExcludedPlaceBaseObstruction318
