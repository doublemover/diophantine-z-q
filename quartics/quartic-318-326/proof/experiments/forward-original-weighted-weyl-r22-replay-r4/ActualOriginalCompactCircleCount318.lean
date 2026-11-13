module
public import ActualOriginalScaledCircle318
public import ActualOriginalFiniteCircleIdentity318
public section
noncomputable section
namespace ActualOriginalCompactCircleCount318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalUniformTranslateSupport318 ActualOriginalAffineInput318
open ActualOriginalScaledCircle318 ActualOriginalFiniteCircleIdentity318
open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The literal scaled weight on the original five integer coordinates. -/
@[expose] def latticeWeight (B : ℝ) (W : Coordinates ℝ → ℝ) (x : Coordinates ℤ) : ℂ :=
  (W (B⁻¹ • integerEmbed x) : ℂ)

/-- One finite set supports every phase at this scale. It is constructed
from the original compact support, before the circle variable is chosen. -/
theorem actual_weight_finite_support (B : ℝ) (hB : B ≠ 0)
    (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W) :
    ∃ s : Finset (Coordinates ℤ), ∀ x ∉ s, latticeWeight B W x = 0 := by
  classical
  let f : Coordinates ℝ → ℂ := fun x => (W x : ℂ)
  have hf : HasCompactSupport f := by
    apply hW.mono
    intro x hx hz
    exact hx (by simp [f,hz])
  have hc := actual_affine_input_compact f hf (0 : Coordinates ℝ) (inv_ne_zero hB)
  obtain ⟨s,hs⟩ := actual_uniform_translate_support (affineInput f 0 B⁻¹) hc
    (isCompact_singleton (x := (0 : Coordinates ℝ)))
  refine ⟨s,fun x hx => ?_⟩
  simpa only [affineInput,f,add_zero,zero_add,latticeWeight] using hs 0 (by simp) x hx

/-- This full lattice zero count uses the same equation and weight as the
Poisson sum. There is no primitive-point filter or replacement quadric. -/
@[expose] def compactZeroCount (κ : ℤ) (B : ℝ) (W : Coordinates ℝ → ℝ) : ℂ :=
  ∑' x : Coordinates ℤ, if equation κ x = 0 then latticeWeight B W x else 0

lemma actual_circle_eq_finite (κ : ℤ) (B : ℝ) (W : Coordinates ℝ → ℝ)
    (s : Finset (Coordinates ℤ)) (hs : ∀ x ∉ s, latticeWeight B W x = 0) (β : ℝ) :
    scaledCircleSum κ β B W = originalCircleSum κ s (latticeWeight B W)
      (β : UnitAddCircle) := by
  classical
  unfold scaledCircleSum
  simp_rw [actual_scaled_weight_fourier]
  change (∑' x : Coordinates ℤ, latticeWeight B W x * fourier (equation κ x) (β : UnitAddCircle)) = _
  rw [tsum_eq_sum (s := s) (fun x hx => by rw [hs x hx,zero_mul])]
  simp only [originalCircleSum,Finset.sum_apply]

lemma actual_zero_count_eq_finite (κ : ℤ) (B : ℝ) (W : Coordinates ℝ → ℝ)
    (s : Finset (Coordinates ℤ)) (hs : ∀ x ∉ s, latticeWeight B W x = 0) :
    compactZeroCount κ B W = originalWeightedZeros κ s (latticeWeight B W) := by
  classical
  unfold compactZeroCount originalWeightedZeros
  apply tsum_eq_sum
  intro x hx
  split_ifs <;> first | exact hs x hx | rfl

/-- Continuity of the full original circle sum follows from one uniformly
finite support, rather than an unproved interchange of an infinite sum. -/
theorem actual_scaled_circle_continuous (κ : ℤ) (B : ℝ) (hB : B ≠ 0)
    (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W) :
    Continuous (fun β : ℝ => scaledCircleSum κ β B W) := by
  obtain ⟨s,hs⟩ := actual_weight_finite_support B hB W hW
  simp_rw [actual_circle_eq_finite κ B W s hs,originalCircleSum,Finset.sum_apply]
  fun_prop

/-- The ACTUAL full Poisson-side circle integral counts exactly the actual
compactly weighted original integer zero locus. No arc estimate is assumed. -/
theorem actual_compact_circle_count (κ : ℤ) (B : ℝ) (hB : B ≠ 0)
    (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W) :
    (∫ β : ℝ in 0..1, scaledCircleSum κ β B W) = compactZeroCount κ B W := by
  obtain ⟨s,hs⟩ := actual_weight_finite_support B hB W hW
  simp_rw [actual_circle_eq_finite κ B W s hs]
  rw [actual_original_circle_interval]
  exact (actual_zero_count_eq_finite κ B W s hs).symm

/-- A nonzero actual count supplies an original integer point on the SAME
support. This statement does not manufacture positivity of the count. -/
theorem actual_point_of_count_ne_zero (κ : ℤ) (B : ℝ) (W : Coordinates ℝ → ℝ)
    (hc : compactZeroCount κ B W ≠ 0) :
    ∃ x : Coordinates ℤ, equation κ x = 0 ∧ W (B⁻¹ • integerEmbed x) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hc
  apply tsum_eq_zero
  intro x
  split_ifs with hx
  · simp only [latticeWeight,h x hx,Complex.ofReal_zero]
  · rfl

end ActualOriginalCompactCircleCount318
