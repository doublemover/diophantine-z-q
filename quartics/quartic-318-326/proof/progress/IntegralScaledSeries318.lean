module
public import IntegralGeometricInverse318
public import ScaledClosedDisc318
public import FormalSeriesNaturality318
public section
namespace IntegralScaledSeries318
open PowerSeries IntegralRingEvaluation318
variable (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
variable {R : Type*} [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R] [NormBoundOne R]
variable (ι : ℤ_[p] →+* R) (D : R)
set_option linter.unusedSectionVars false

/-- The coefficient parameter D is arbitrary in the integral ring, not necessarily in Qp. -/
@[expose] noncomputable def H : PowerSeries R :=
  rescale D ((ScaledCoefficients318.Hscaled p hp 1 (by simp)).map ι)
@[expose] noncomputable def B : PowerSeries R :=
  rescale D ((ScaledCoefficients318.Bscaled p hp 1 (by simp)).map ι)
@[expose] def parameter : R := D*(p : R)^4
@[expose] noncomputable def integral : PowerSeries R := -X*(H p hp ι D).subst (X^4 : PowerSeries R)
@[expose] noncomputable def differential : PowerSeries R := (B p hp ι D).subst (X^4 : PowerSeries R)
@[expose] noncomputable def branch : PowerSeries R :=
  (1-C (parameter p D)*X^4)*differential p hp ι D

variable (hι : Isometry ι)
include hι

local instance : NormBoundOne ℤ_[p] := ⟨PadicInt.norm_le_one⟩

theorem H_restricted : IsRestricted 1 (H p hp ι D) :=
  rescale_restricted R D _
    (restricted_map ℤ_[p] ι hι _ (ScaledClosedDisc318.Hscaled_restricted p hp 1 (by simp)))

theorem B_restricted : IsRestricted 1 (B p hp ι D) :=
  rescale_restricted R D _
    (restricted_map ℤ_[p] ι hι _ (ScaledClosedDisc318.Bscaled_restricted p hp 1 (by simp)))

theorem integral_restricted : IsRestricted 1 (integral p hp ι D) :=
  (X_restricted R).neg.mul (subst_restricted R _ _ (H_restricted p hp ι D hι)
    ((X_restricted R).pow 4) (by simp))

theorem differential_restricted : IsRestricted 1 (differential p hp ι D) :=
  subst_restricted R _ _ (B_restricted p hp ι D hι) ((X_restricted R).pow 4) (by simp)

theorem branch_restricted : IsRestricted 1 (branch p hp ι D) :=
  ((isRestricted_one 1).sub ((isRestricted_C 1 _).mul ((X_restricted R).pow 4))).mul
    (differential_restricted p hp ι D hι)

omit hι
variable {K : Type*} [Field K] [CharZero K] (φ : R →+* K) (ψ : ℚ_[p] →+* K)
variable (hcompat : ∀ z : ℤ_[p], φ (ι z) = ψ (z : ℚ_[p]))
include hcompat

theorem map_H : (H p hp ι D).map φ =
    rescale (φ (parameter p D)) (GenericFormalDifferential318.H (K := K)) := by
  ext n
  simp only [H, coeff_map, coeff_rescale, map_mul, map_pow, hcompat,
    ScaledCoefficients318.coeff_Hscaled, ScaledCoefficients318.coe_hIntegralCoefficient,
    ScaledCoefficients318.hCoefficient, one_pow, mul_one, map_mul, map_pow, map_ratCast,
    map_natCast, parameter, GenericFormalDifferential318.H, coeff_map,
    FormalDifferential318.coeff_H, Rat.coe_castHom, mul_pow, ←pow_mul]
  ring

theorem map_B : (B p hp ι D).map φ =
    rescale (φ (parameter p D)) (GenericFormalDifferential318.B (K := K)) := by
  ext n
  simp only [B, coeff_map, coeff_rescale, map_mul, map_pow, hcompat,
    ScaledCoefficients318.coeff_Bscaled, ScaledCoefficients318.coe_bIntegralCoefficient,
    ScaledCoefficients318.bCoefficient, one_pow, mul_one, map_mul, map_pow, map_ratCast,
    map_natCast, parameter, GenericFormalDifferential318.B, coeff_map,
    FormalDifferential318.coeff_B, Rat.coe_castHom, mul_pow, ←pow_mul]
  ring

theorem map_integral : (integral p hp ι D).map φ =
    GenericFormalDifferential318.integral (φ (parameter p D)) := by
  have hx : HasSubst (X^4 : PowerSeries R) := .of_constantCoeff_zero
    (by change constantCoeff (X^4 : PowerSeries R)=0; simp)
  rw [integral, map_mul, map_neg, map_X,
    ScaledFormalSeries318.map_subst_univariate _ _ _ hx,
    map_H p hp ι D φ ψ hcompat, map_pow, map_X, ScaledFormalSeries318.rescale_subst_fourth]
  rfl

theorem map_differential : (differential p hp ι D).map φ =
    GenericFormalDifferential318.differential (φ (parameter p D)) := by
  have hx : HasSubst (X^4 : PowerSeries R) := .of_constantCoeff_zero
    (by change constantCoeff (X^4 : PowerSeries R)=0; simp)
  rw [differential, ScaledFormalSeries318.map_subst_univariate _ _ _ hx,
    map_B p hp ι D φ ψ hcompat, map_pow, map_X, ScaledFormalSeries318.rescale_subst_fourth]
  rfl

theorem map_branch : (branch p hp ι D).map φ =
    GenericFormalDifferential318.branch (φ (parameter p D)) := by
  simp only [branch, map_mul, map_sub, map_one, map_C, map_pow, map_X,
    map_differential p hp ι D φ ψ hcompat, GenericFormalDifferential318.branch,
    GenericFormalDifferential318.argument]

/-- Actual formal addition for arbitrary integral D, with no descent-to-Qp condition. -/
theorem formal_addition (hφ : Function.Injective φ) :
    (integral p hp ι D).subst
      (IntegralFormalAddition318.f (parameter p D) (branch p hp ι D)) =
    (integral p hp ι D).subst (IntegralFormalAddition318.x (R := R)) +
      (integral p hp ι D).subst (IntegralFormalAddition318.a (R := R)) :=
  IntegralFormalAddition318.formal_addition φ hφ _ _ _
    (map_integral p hp ι D φ ψ hcompat) (map_branch p hp ι D φ ψ hcompat)

end IntegralScaledSeries318
#print axioms IntegralScaledSeries318.H_restricted
#print axioms IntegralScaledSeries318.map_integral
#print axioms IntegralScaledSeries318.map_branch
#print axioms IntegralScaledSeries318.formal_addition
