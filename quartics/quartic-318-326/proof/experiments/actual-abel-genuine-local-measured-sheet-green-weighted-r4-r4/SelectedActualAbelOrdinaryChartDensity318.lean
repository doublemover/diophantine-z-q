module

public import SelectedOriginalAbelMeasuredCover318
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

noncomputable section

open Matrix MeasureTheory Set UpperHalfPlane
open scoped BigOperators ENNReal NNReal Classical ComplexConjugate
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedAbelSumGramProductIntegral318
open SelectedOriginalAbelMeasuredCover318

namespace SelectedActualAbelOrdinaryChartDensity318

variable {M g : ℕ}

/-- Evaluations of the original ordered forms at the actual periods,
without the hyperbolic factors. The determinant is unchanged by using
the transpose derivative convention. -/
def periodMatrix (f : Fin g → Form M) (τ : Fin g → UpperHalfPlane) :
    Matrix (Fin g) (Fin g) ℂ :=
  fun i k => f i (τ k)

/-- The existing Petersson density, read along the actual ordered period projection,
contains exactly one imaginary square per source variable. -/
theorem original_positiveDensity_period
    (f : Fin g → Form M) (τ : Fin g → UpperHalfPlane) :
    (positiveDensity f (fun k => quotientMap M (τ k)) : ℝ) =
      Complex.normSq (periodMatrix f τ).det * ∏ k, (τ k).im ^ 2 := by
  classical
  let z : Domain M g := fun k => quotientMap M (τ k)
  let A : Matrix (Fin g) (Fin g) ℂ := fun i k => f i (τ k) * ((τ k).im : ℂ)
  have hc (i j k : Fin g) :
      cross (f i) (f j) (z k) = conj (A i k) * A j k := by
    change cross (f i) (f j) (quotientMap M (τ k)) = _
    rw [cross_projection]
    simp only [A, map_mul, Complex.conj_ofReal]
    ring
  have hA : complexDensity f z = (Complex.normSq A.det : ℂ) := by
    unfold complexDensity summand
    simp_rw [hc]
    exact expanded_density A
  have hw : (positiveDensity f z : ℝ) = Complex.normSq A.det := by
    have he := congrArg Complex.re ((image_of_positiveDensity f z).symm.trans hA)
    simpa only [Complex.ofReal_re] using he
  have hM : A = periodMatrix f τ * Matrix.diagonal (fun k => ((τ k).im : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal] <;> rfl
  calc
    (positiveDensity f z : ℝ) = Complex.normSq A.det := hw
    _ = Complex.normSq (periodMatrix f τ).det *
        ∏ k, Complex.normSq ((τ k).im : ℂ) := by
      rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
    _ = Complex.normSq (periodMatrix f τ).det * ∏ k, (τ k).im ^ 2 := by
      simp only [Complex.normSq_ofReal, pow_two]

/-- The literal hyperbolic reference densities cancel in the original
Abel9 positive density. The determinant on the right is from the same
ordered period matrix with no rescaling of the forms or change of basis. -/
theorem original_density_cancels_hyperbolic_weight
    (f : Fin g → Form M) (τ : Fin g → UpperHalfPlane) :
    (positiveDensity f (fun k => quotientMap M (τ k)) : ℝ) *
        (∏ k : Fin g, (1 / (τ k).im) ^ 2) =
      Complex.normSq (periodMatrix f τ).det := by
  rw [original_positiveDensity_period, mul_assoc, ← Finset.prod_mul_distrib]
  have h (k : Fin g) : (τ k).im ^ 2 * (1 / (τ k).im) ^ 2 = 1 := by
    rw [← mul_pow]
    have hn : (τ k).im ≠ 0 := (τ k).im_pos.ne'
    have he : (τ k).im * (1 / (τ k).im) = 1 := by
      rw [one_div, mul_inv_cancel₀ hn]
    rw [he, one_pow]
  simp only [h, Finset.prod_const_one, mul_one]

end SelectedActualAbelOrdinaryChartDensity318

#print axioms SelectedActualAbelOrdinaryChartDensity318.original_density_cancels_hyperbolic_weight
