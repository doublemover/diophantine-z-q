module
public import ActualOriginalTwistedWeight318
public section
noncomputable section
namespace ActualOriginalCoordinateFrequency318
open QuadricCRTAssembly318 ActualOriginalTwistedWeight318
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 16000000

@[expose] def pA : Coordinates ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ((ℝ×ℝ)×ℝ))
@[expose] def pB : Coordinates ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ((ℝ×ℝ)×ℝ))
@[expose] def pC : Coordinates ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ×ℝ) ((ℝ×ℝ)×ℝ)))
@[expose] def pD : Coordinates ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ×ℝ) ((ℝ×ℝ)×ℝ)))
@[expose] def pW : Coordinates ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ×ℝ) ((ℝ×ℝ)×ℝ))

/-- The literal coordinate dot product paired against the original
five-coordinate source. The ambient norm and volume are unchanged. -/
@[expose] def frequency (y : Coordinates ℝ) : Coordinates ℝ →L[ℝ] ℝ :=
  y.1.1 • pA + y.1.2 • pB + y.2.1.1 • pC + y.2.1.2 • pD + y.2.2 • pW

@[expose] def dot (y x : Coordinates ℝ) : ℝ :=
  y.1.1*x.1.1+y.1.2*x.1.2+y.2.1.1*x.2.1.1+y.2.1.2*x.2.1.2+y.2.2*x.2.2

lemma actual_frequency_apply (y x : Coordinates ℝ) : frequency y x = dot y x := by
  simp [frequency,pA,pB,pC,pD,pW,dot]

/-- Every original coordinate is detected by an actual unit coordinate
vector. This proves the norm comparison required to consume full dual decay,
without silently using a Euclidean norm on the original product space. -/
lemma actual_coordinate_norm_le_dual (y : Coordinates ℝ) : ‖y‖ ≤ ‖frequency y‖ := by
  have ha := (frequency y).le_opNorm (((1,0),(0,0),0) : Coordinates ℝ)
  have hb := (frequency y).le_opNorm (((0,1),(0,0),0) : Coordinates ℝ)
  have hc := (frequency y).le_opNorm (((0,0),(1,0),0) : Coordinates ℝ)
  have hd := (frequency y).le_opNorm (((0,0),(0,1),0) : Coordinates ℝ)
  have hw := (frequency y).le_opNorm (((0,0),(0,0),1) : Coordinates ℝ)
  norm_num [actual_frequency_apply,dot,Prod.norm_def] at ha hb hc hd hw
  exact max_le (max_le ha hb) (max_le (max_le hc hd) hw)

@[expose] def originalCoordinateFourier (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (y : Coordinates ℝ) : ℂ := originalTwistedFourier κ β W (frequency y)

lemma actual_coordinate_fourier_integral (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (y : Coordinates ℝ) : originalCoordinateFourier κ β W y =
      ∫ x : Coordinates ℝ, Real.fourierChar (-dot y x) • twistedWeight κ β W x := by
  simp only [originalCoordinateFourier,originalTwistedFourier,actual_frequency_apply]

/-- All-frequency decay on the literal original coordinate dual. The
constant may depend on the fixed β, as required by this bounded statement. -/
theorem actual_original_coordinate_decay (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (n : ℕ) :
    ∃ C : ℝ, ∀ y : Coordinates ℝ, ‖y‖^n * ‖originalCoordinateFourier κ β W y‖ ≤ C := by
  obtain ⟨C,hC⟩ := actual_original_full_dual_decay κ β W hW hWc n
  refine ⟨C,fun y => ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (actual_coordinate_norm_le_dual y) n)
    (norm_nonneg _)).trans (hC (frequency y))

end ActualOriginalCoordinateFrequency318
