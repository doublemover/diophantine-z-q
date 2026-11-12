module
public import PELOriginalPeriodMetricDeterminant318
public import MobiusPoincarePullback318
public import PeterssonSectionNorm318
public import Mathlib.Analysis.Calculus.Deriv.Comp
public section
noncomputable section
namespace PELOriginalPulledPeriodMetric318
open PELOriginalSiegelMatrix318 PELOriginalSiegelNormalization318
open PELOriginalPeriodMatrixDerivative318 PELOriginalPeriodMetricDeterminant318
open MobiusPoincarePullback318 PeterssonSectionNorm318

lemma pulled_derivative (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) :
    deriv (fun w => omega (f w)) z=deriv f z • derivative (f z) := by
  exact ((hasDerivAt_omega (f z) (parameter_ne (f z) hu)).scomp z hf.hasDerivAt).deriv
lemma det_scalar (a : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (a • M).det=a^2*M.det := by
  simp only [Matrix.det_fin_two,Matrix.smul_apply,smul_eq_mul]
  ring

/-- Exact determinant norm of the ACTUAL composite period matrix in an
arbitrary original holomorphic uniformizing coordinate. -/
theorem determinant_density (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) :
    ‖(deriv (fun w => omega (f w)) z).det‖=
      density f z*(imaginary (f z)).det := by
  rw [pulled_derivative f z hf hu,det_scalar,norm_mul,norm_pow,
    derivative_determinant_norm (f z) hu,imaginary_determinant (f z) hu]
  unfold density
  have hn : Complex.normSq (f z)≠0 :=
    (Complex.normSq_pos.mpr (parameter_ne (f z) hu)).ne'
  field_simp [hn,hu.ne']
  ring

/-- Literal factor4 from the repository's cotangent norm2/sqrt(h), not a
renormalized metric convention. The period determinant is a genuine
quadratic-differential coefficient under coordinate change. -/
theorem determinant_petersson (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hu : 0<(f z).im) (hd : deriv f z≠0) :
    quadraticNorm (density f z) ((deriv (fun w => omega (f w)) z).det)=
      4*(imaginary (f z)).det := by
  have hh : 0<density f z := div_pos
    (sq_pos_of_pos (norm_pos_iff.mpr hd)) (sq_pos_of_pos hu)
  rw [quadraticNorm_formula _ hh,determinant_density f z hf hu]
  field_simp [hh.ne']
end PELOriginalPulledPeriodMetric318
