module
public import QuaternionicMobiusPeriods318
public import HolomorphicPoincare318
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public section
noncomputable section
namespace MobiusPoincarePullback318
open QuaternionicMobiusPeriods318 QuaternionicRealPeriod318

/-- The exact derivative of the original determinant-one matrix action. -/
theorem hasDerivAt_mobius (g : RealMatrices) (hg : g.det = 1) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (mobius g) (1 / denominator g z ^ 2) z := by
  have hn := ((hasDerivAt_const z (g 0 0 : ℂ)).mul (hasDerivAt_id z)).add_const (g 0 1 : ℂ)
  have hd := ((hasDerivAt_const z (g 1 0 : ℂ)).mul (hasDerivAt_id z)).add_const (g 1 1 : ℂ)
  have h : HasDerivAt (mobius g)
      (((g 0 0 : ℂ)*denominator g z-((g 0 0 : ℂ)*z+(g 0 1 : ℂ))*(g 1 0 : ℂ))/denominator g z^2) z := by
    simpa only [zero_mul,zero_add,mul_one] using hn.div hd (denominator_ne g hg z hz)
  have hdet : (g 0 0 : ℂ)*(g 1 1 : ℂ)-(g 0 1 : ℂ)*(g 1 0 : ℂ)=1 := by
    exact_mod_cast (show g 0 0*g 1 1-g 0 1*g 1 0=1 by simpa only [Matrix.det_fin_two] using hg)
  convert h using 1
  congr 1
  unfold denominator
  linear_combination -hdet

/-- Literal local Poincare density; independent of the auxiliary real-axis notation. -/
@[expose] def density (f : ℂ → ℂ) (z : ℂ) : ℝ := ‖deriv f z‖^2/(f z).im^2

/-- Postcomposition by an actual original determinant-one real matrix
preserves the full derivative-weighted density, not just its value on points. -/
theorem density_mobius (g : RealMatrices) (hg : g.det = 1) (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z) (hz : 0 < (f z).im) :
    density (fun w => mobius g (f w)) z = density f z := by
  have hd := (hasDerivAt_mobius g hg (f z) hz).comp z hf.hasDerivAt
  have hn : ‖denominator g (f z)‖ ≠ 0 := norm_ne_zero_iff.mpr (denominator_ne g hg (f z) hz)
  rw [density,density,hd.deriv,mobius_im g hg]
  simp only [norm_mul,norm_div,norm_one,norm_pow,Complex.normSq_eq_norm_sq]
  field_simp [hn,hz.ne']
  <;> ring

lemma density_eq_coefficient (f : ℂ → ℂ) (w : ℝ × ℝ) :
    density f (HarmonicAxis318.coord w) = HolomorphicPoincare318.coefficient f w := rfl
end MobiusPoincarePullback318
