module
public import ThreeJAnalyticRamificationDivisor318
public section
noncomputable section
namespace ThreeJDerivativeComparison318
open Polynomial ThreeJLaurentEquiv318 ThreeJDerivativeOpen318
open ThreeJRamificationParameters318 ThreeJAnalyticRamificationDivisor318
open ThreeCompactParameter318
set_option maxHeartbeats 1000000

/-- Evaluation on every nonzero finite parameter, including the unramified
point -27 omitted by the smaller arithmetic-open localization. -/
@[expose] def evaluation (z : ℂ) (hz : z ≠ 0) : Laurent →ₐ[ℚ] ℂ :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval (R:=ℚ) z) (Polynomial.X:ℚ[X])
    (by simpa only [Polynomial.aeval_X] using isUnit_iff_ne_zero.mpr hz)
lemma evaluation_t (z : ℂ) (hz : z ≠ 0) : evaluation z hz ProjectiveLineOverlap318.t=z := by
  simp only [evaluation,ProjectiveLineOverlap318.t,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  exact Polynomial.aeval_X z
lemma evaluation_s (z : ℂ) (hz : z ≠ 0) : evaluation z hz ProjectiveLineOverlap318.s=z⁻¹ := by
  have h := congrArg (evaluation z hz) ProjectiveLineOverlap318.ts
  simp only [map_mul,map_one,evaluation_t] at h
  exact (inv_eq_of_mul_eq_one_right h).symm

theorem evaluation_derivative (z : ℂ) (hz : z ≠ 0) :
    evaluation z hz derivativeImage=z⁻¹*(z+243)^2*D z := by
  rw [derivative_factorization]
  simp only [map_mul,map_add,map_pow,map_ofNat,map_sub,
    evaluation_t,evaluation_s,ellipticFactor,D]

/-- The actual scheme derivative localization selects exactly the points
whose exhaustive analytic ramification coefficient is zero on the Laurent chart. -/
theorem derivative_unit_iff_coefficient_zero (z : ℂ) (hz : z ≠ 0) :
    IsUnit (evaluation z hz derivativeImage) ↔ ramification (finitePoint z)=0 := by
  rw [isUnit_iff_ne_zero,evaluation_derivative,ramification_finite]
  have hd : D z=0 ↔ z=rootPlus ∨ z=rootMinus := D_zero_iff z
  have he : z⁻¹*(z+243)^2*D z=0 ↔
      ThreeJRamificationParameters318.multiplicity z≠0 := by
    rw [multiplicity_nonzero_iff]
    simp only [mul_eq_zero,inv_eq_zero,pow_eq_zero_iff (by decide : 2 ≠ 0),
      add_eq_zero_iff_eq_neg,hz,false_or,hd]
  exact he.not.trans (not_not)

theorem neg27_in_derivative_open :
    IsUnit (evaluation (-27) (by norm_num) derivativeImage) := by
  rw [isUnit_iff_ne_zero,evaluation_derivative]
  norm_num [D]

/-- Every original Laurent complex point outside the explicit divisor
admits an actual algebraic lift through the etale scheme restriction. -/
@[expose] def etaleEvaluation (z : ℂ) (hz : z ≠ 0)
    (h : ramification (finitePoint z)=0) : ThreeJDerivativeOpen318.Ring →ₐ[ℚ] ℂ :=
  IsLocalization.Away.liftAlgHom (f:=evaluation z hz) derivativeImage
    ((derivative_unit_iff_coefficient_zero z hz).mpr h)

lemma etaleEvaluation_inclusion (z : ℂ) (hz : z ≠ 0)
    (h : ramification (finitePoint z)=0) (a : Laurent) :
    etaleEvaluation z hz h (algebraMap Laurent ThreeJDerivativeOpen318.Ring a)=evaluation z hz a := by
  simp only [etaleEvaluation,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl

end ThreeJDerivativeComparison318
