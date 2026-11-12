module
public import PELOriginalKernelDeterminantLine318
public import PELOriginalPeriodMetricDeterminant318
public section
noncomputable section
namespace PELOriginalPolarizedKernelMetric318
open QuaternionicRealPeriod318 PELOriginalSiegelMatrix318
open PELOriginalFlatPeriodKernel318 PELOriginalPeriodKernelConnection318

@[expose] def conjugate (p : Ambient) : Ambient :=
  (fun i => star (p.1 i),fun i => star (p.2 i))
/-- The actual polarized Hermitian form on the period-kernel plane,
constructed from its original alternating form and real conjugation.
The factor I/2 is explicit and retained throughout. -/
@[expose] def metric (τ : ℂ) (v w : ComplexVectors) : ℂ :=
  Complex.I*symplectic (kernelLift τ v) (conjugate (kernelLift τ w))/2
lemma metric_formula (τ : ℂ) (v w : ComplexVectors) :
    metric τ v w=∑ i : Fin 2, ∑ j : Fin 2,
      (imaginary τ i j:ℂ)*v i*star (w j) := by
  have hs : omega τ 1 0=omega τ 0 1 := rfl
  apply Complex.ext <;>
    simp [metric,symplectic,kernelLift,conjugate,dotProduct,Matrix.mulVec,
      Fin.sum_univ_two,imaginary,hs,Complex.mul_re,Complex.mul_im,
      Complex.div_re,Complex.div_im,Complex.star_def] <;> ring
lemma metric_hermitian (τ : ℂ) (v w : ComplexVectors) :
    metric τ w v=star (metric τ v w) := by
  have hs : imaginary τ 1 0=imaginary τ 0 1 := rfl
  rw [metric_formula,metric_formula]
  apply Complex.ext <;>
    simp [Fin.sum_univ_two,hs,Complex.mul_re,Complex.mul_im,Complex.star_def] <;> ring
lemma metric_diagonal_real (τ : ℂ) (v : ComplexVectors) :
    (metric τ v v).re=energy τ (fun i => (v i).re)+energy τ (fun i => (v i).im) := by
  rw [metric_formula]
  have hs : imaginary τ 1 0=imaginary τ 0 1 := rfl
  simp [Fin.sum_univ_two,energy,hs,Complex.mul_re,Complex.mul_im,Complex.star_def]
  ring
lemma energy_nonnegative (τ : ℂ) (hτ : 0<τ.im) (v : Fin 2 → ℝ) : 0≤energy τ v := by
  by_cases hv : v=0
  · subst v;simp [energy]
  · exact (positive τ hτ v hv).le

/-- Strict positivity on EVERY nonzero complex kernel vector, produced
from the actual original Siegel positivity, not assumed as a metric input. -/
theorem metric_positive (τ : ℂ) (hτ : 0<τ.im) (v : ComplexVectors) (hv : v≠0) :
    0<(metric τ v v).re := by
  rw [metric_diagonal_real]
  by_cases hr : (fun i => (v i).re)=(0:Fin 2 → ℝ)
  · have hi : (fun i => (v i).im)≠(0:Fin 2 → ℝ) := by
      intro hi
      apply hv
      ext i
      exact Complex.ext (congrFun hr i) (congrFun hi i)
    exact add_pos_of_nonneg_of_pos (energy_nonnegative τ hτ _) (positive τ hτ _ hi)
  · exact add_pos_of_pos_of_nonneg (positive τ hτ _ hr) (energy_nonnegative τ hτ _)

/-- Its actual coordinate matrix is the imaginary part of the SAME
original period matrix, giving the already proved metric determinant. -/
lemma metric_basis (τ : ℂ) (i j : Fin 2) :
    metric τ (Pi.single i 1) (Pi.single j 1)=(imaginary τ i j:ℂ) := by
  rw [metric_formula]
  simp
end PELOriginalPolarizedKernelMetric318
