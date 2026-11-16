module
public import ActualOriginalQuadraticEnergyCount318
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public section
noncomputable section
namespace ActualOriginalFiniteFourierEnergy318
open MeasureTheory ActualOriginalFiniteCircleIdentity318
open scoped BigOperators ComplexConjugate
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

@[expose] def frequencySum {α : Type*} (s : Finset α) (f : α → ℤ)
    (θ : AddCircle (1 : ℝ)) : ℂ := ∑ x∈s, fourier (f x) θ
@[expose] def frequencyEnergy {α : Type*} (s : Finset α) (f : α → ℤ) : Finset (α×α) := by
  classical
  exact (s.product s).filter (fun p => f p.1=f p.2)

lemma actual_frequency_difference {α : Type*} (s : Finset α) (f : α → ℤ)
    (θ : AddCircle (1 : ℝ)) :
    frequencySum s f θ*conj (frequencySum s f θ)=
      frequencySum (s.product s) (fun p => f p.1-f p.2) θ := by
  classical
  simp only [frequencySum,map_sum,Finset.sum_mul,Finset.mul_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [sub_eq_add_neg,←fourier_neg,←fourier_add]

lemma actual_frequency_integral {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∫ θ : AddCircle (1 : ℝ), frequencySum s f θ ∂haarAddCircle)=
      ∑ x∈s, if f x=0 then (1 : ℂ) else 0 := by
  classical
  have hi (x : α) (_ : x∈s) : Integrable (fun θ : AddCircle (1 : ℝ) => fourier (f x) θ) haarAddCircle :=
    (fourier (f x)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [frequencySum,integral_finsetSum s hi]
  apply Finset.sum_congr rfl
  intro x hx
  simpa only [fourierCoeff,neg_zero,fourier_zero,one_smul] using actual_character_coefficient_zero (f x)

/-- Exact finite Parseval/orthogonality, with period one Haar mass one.
This is proved by finite expansion rather than an assumed L2 identity. -/
theorem actual_frequency_second_moment {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∫ θ : AddCircle (1 : ℝ), ‖frequencySum s f θ‖^2 ∂haarAddCircle)=
      ((frequencyEnergy s f).card : ℝ) := by
  classical
  have he (θ : AddCircle (1 : ℝ)) : ((‖frequencySum s f θ‖^2 : ℝ) : ℂ)=
      frequencySum (s.product s) (fun p => f p.1-f p.2) θ := by
    rw [←Complex.normSq_eq_norm_sq,←Complex.mul_conj,actual_frequency_difference]
  apply Complex.ofReal_injective
  rw [←integral_complex_ofReal]
  simp_rw [he]
  rw [actual_frequency_integral]
  simp only [sub_eq_zero,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,
    frequencyEnergy,Complex.ofReal_natCast]

end ActualOriginalFiniteFourierEnergy318
