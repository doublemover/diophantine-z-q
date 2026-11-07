module
public import ScaledFormalSeries318
public section
namespace FormalSeriesNaturality318
open PowerSeries GenericFormalDifferential318
variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
variable (φ : K →+* L)

theorem map_H : (H (K := K)).map φ = H (K := L) := by
  ext n
  simp only [H, coeff_map, FormalDifferential318.coeff_H, Rat.coe_castHom, map_ratCast]

theorem map_B : (B (K := K)).map φ = B (K := L) := by
  ext n
  simp only [B, coeff_map, FormalDifferential318.coeff_B, Rat.coe_castHom, map_ratCast]

theorem map_argument (D : K) : (argument D).map φ = argument (φ D) := by
  simp only [argument, map_mul, map_C, map_pow, map_X]

theorem map_integral (D : K) : (integral D).map φ = integral (φ D) := by
  have hs : HasSubst (argument D) := .of_constantCoeff_zero
    (by change constantCoeff (argument D)=0; simp [argument])
  rw [integral, map_mul, map_neg, map_X,
    ScaledFormalSeries318.map_subst_univariate _ _ _ hs, map_H, map_argument]
  rfl

theorem map_differential (D : K) : (differential D).map φ = differential (φ D) := by
  have hs : HasSubst (argument D) := .of_constantCoeff_zero
    (by change constantCoeff (argument D)=0; simp [argument])
  rw [differential, ScaledFormalSeries318.map_subst_univariate _ _ _ hs, map_B, map_argument]
  rfl

theorem map_branch (D : K) : (branch D).map φ = branch (φ D) := by
  simp only [branch, map_mul, map_sub, map_one, map_argument, map_differential]

end FormalSeriesNaturality318
#print axioms FormalSeriesNaturality318.map_integral
#print axioms FormalSeriesNaturality318.map_branch
