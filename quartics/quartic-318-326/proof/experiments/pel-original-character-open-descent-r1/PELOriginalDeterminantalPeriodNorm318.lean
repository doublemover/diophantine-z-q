module
public import PELOriginalDeterminantalPeriodPairing318
public section
noncomputable section
namespace PELOriginalDeterminantalPeriodNorm318
open PELOriginalSiegelMatrix318 PELOriginalKernelDeterminantLine318
open PELOriginalNormedKernelDeterminant318 PELOriginalDeterminantMetricTransition318
open PELOriginalDeterminantalPeriodPairing318 PELOriginalSecondFundamentalMetric318
open PeterssonSectionNorm318 MobiusPoincarePullback318
open scoped TensorProduct

@[expose] def squareMetricFrame (τ : ℂ) (hτ : 0<τ.im) : Square τ ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (metricFrame τ hτ) (metricFrame τ hτ)).trans (TensorProduct.lid ℂ ℂ)
lemma squareMetricFrame_formula (τ : ℂ) (hτ : 0<τ.im) (x : Square τ) :
    squareMetricFrame τ hτ x=((imaginary τ).det:ℂ)*squareCoordinate τ x := by
  have hs : (scale τ:ℂ)^2=((imaginary τ).det:ℂ) := by
    have h := Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp (scale_positive τ hτ)))
    exact_mod_cast h
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
      simp only [squareMetricFrame,LinearEquiv.trans_apply,TensorProduct.congr_tmul,
        TensorProduct.lid_tmul,smul_eq_mul,squareCoordinate_pure]
      change ((scale τ:ℂ)*coordinate τ v)*((scale τ:ℂ)*coordinate τ w)=_
      rw [←hs]
      ring
  | add x y hx hy => simp only [map_add,hx,hy,mul_add]

@[expose] def squareNormedGroup (τ : ℂ) (hτ : 0<τ.im) : NormedAddCommGroup (Square τ) :=
  NormedAddCommGroup.induced _ ℂ (squareMetricFrame τ hτ).toAddMonoidHom
    (squareMetricFrame τ hτ).injective
@[expose] def squareNormedSpace (τ : ℂ) (hτ : 0<τ.im) :
    letI := squareNormedGroup τ hτ
    NormedSpace ℂ (Square τ) := by
  letI := squareNormedGroup τ hτ
  refine { norm_smul_le := ?_ }
  intro a x
  change ‖squareMetricFrame τ hτ (a • x)‖≤‖a‖*‖squareMetricFrame τ hτ x‖
  rw [map_smul,norm_smul]
@[expose] def squareNorm (τ : ℂ) (hτ : 0<τ.im) (x : Square τ) : ℝ :=
  ‖squareMetricFrame τ hτ x‖
lemma squareNorm_formula (τ : ℂ) (hτ : 0<τ.im) (x : Square τ) :
    squareNorm τ hτ x=(imaginary τ).det*‖squareCoordinate τ x‖ := by
  unfold squareNorm
  rw [squareMetricFrame_formula,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos (Real.sqrt_pos.mp (scale_positive τ hτ))]

/-- Whole norm identity for the genuine determinant-comparison map,
not just for a distinguished section or frame. The literal factor4
comes from the existing cotangent norm2/sqrt(h), and is not suppressed. -/
theorem comparison_norm (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (hd : deriv f z≠0) (x : Square (f z)) :
    quadraticNorm (density f z) (comparison f z hf hu hd x)=4*squareNorm (f z) hu x := by
  rw [comparison_formula,mul_comm (secondMatrix f z).det,quadraticNorm_mul,
    secondMatrix_petersson f z hf hu hd,squareNorm_formula]
  ring
end PELOriginalDeterminantalPeriodNorm318
