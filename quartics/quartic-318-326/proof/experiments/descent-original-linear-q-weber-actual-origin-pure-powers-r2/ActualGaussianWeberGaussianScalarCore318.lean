module
public import ActualGaussianWeberQuarterTurnAdd318
public import Mathlib.Tactic.Abel
public section
noncomputable section

namespace ActualGaussianWeberGaussianScalarSpecialization318

open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberQuarterTurnAdd318

variable {K : Type*} [Field K] [DecidableEq K]

/-- The actual Gaussian-coordinate endomorphism [a+bi], using signed
integer multiplication on the stock elliptic-curve group. -/
@[expose] def gaussian (h2 : (2:K) ≠ 0) (i : K) (hi : i^2 = -1) (a b : ℤ) :
    WP K →+ WP K where
  toFun P := a • P+b • turn h2 i hi P
  map_zero' := by
    have ht : turn h2 i hi (0:WP K)=0 := rfl
    simp only [ht,smul_zero,add_zero]
  map_add' P Q := by
    simp only [turn_add,zsmul_add]
    abel

end ActualGaussianWeberGaussianScalarSpecialization318
