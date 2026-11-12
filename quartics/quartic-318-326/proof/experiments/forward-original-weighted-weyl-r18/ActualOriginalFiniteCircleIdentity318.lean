module
public import ActualOriginalSchwartzDensity318
public import Mathlib.Analysis.Fourier.AddCircle
public section
noncomputable section
namespace ActualOriginalFiniteCircleIdentity318
open QuadricCRTAssembly318 MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 16000000

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- A finite weighted exponential sum on the ORIGINAL integral quadric.
The circle has period ONE and normalized Haar mass ONE. -/
@[expose] def originalCircleSum (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) : AddCircle (1 : ℝ) → ℂ :=
  ∑ x ∈ s, fun θ => w x * fourier (equation κ x) θ

@[expose] def originalWeightedZeros (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) : ℂ :=
  ∑ x ∈ s, if equation κ x = 0 then w x else 0

lemma actual_character_coefficient_zero (n : ℤ) :
    fourierCoeff (T := (1 : ℝ)) (fourier n) 0 = if n = 0 then 1 else 0 := by
  rw [fourierCoeff_fourier]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn, Ne.symm hn]

/-- Exact orthogonality, not a major/minor arc estimate. Every point in
the supplied finite set is counted with its original weight precisely when
the original integer equation vanishes. -/
theorem actual_original_circle_coefficient (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) :
    fourierCoeff (originalCircleSum κ s w) 0 = originalWeightedZeros κ s w := by
  classical
  have hi (x : Coordinates ℤ) (_ : x ∈ s) :
      Integrable (fun θ : AddCircle (1 : ℝ) => w x * fourier (equation κ x) θ)
        haarAddCircle :=
    (continuous_const.mul (fourier (equation κ x)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := congrFun (fourierCoeff.sum s
    (fun x (θ : AddCircle (1 : ℝ)) => w x * fourier (equation κ x) θ) hi) 0
  simp only [Finset.sum_apply] at he
  change fourierCoeff (originalCircleSum κ s w) 0 = _ at he
  rw [he]
  change (∑ x ∈ s, fourierCoeff (fun θ : AddCircle (1 : ℝ) =>
    w x * fourier (equation κ x) θ) 0) = _
  unfold originalWeightedZeros
  apply Finset.sum_congr rfl
  intro x hx
  rw [fourierCoeff.const_mul,actual_character_coefficient_zero]
  split_ifs <;> simp

/-- The same exact identity as an ordinary real integral over [0,1],
with no change of measure or unmentioned scale factor. -/
theorem actual_original_circle_interval (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) :
    (∫ θ : ℝ in 0..1, originalCircleSum κ s w (θ : AddCircle (1 : ℝ))) =
      originalWeightedZeros κ s w := by
  have he := fourierCoeff_eq_intervalIntegral (originalCircleSum κ s w) 0 0
  have hc := actual_original_circle_coefficient κ s w
  rw [he] at hc
  simpa only [neg_zero,fourier_zero,one_smul,zero_add,div_one] using hc

/-- On real representatives the phase is exactly exp(2*pi*i*Q(x)*θ).
This positive circle-method phase is explicit; the earlier ambient Fourier
transform uses the negative phase and therefore the negated frequency. -/
theorem actual_original_circle_phase (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) (θ : ℝ) :
    originalCircleSum κ s w (θ : AddCircle (1 : ℝ)) =
      ∑ x ∈ s, w x * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (equation κ x : ℂ) * (θ : ℂ)) := by
  unfold originalCircleSum
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one,div_one]

end ActualOriginalFiniteCircleIdentity318
