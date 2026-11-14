module
public import ActualOriginalPoissonSummation318
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Algebra.ConstMulAction
public section
noncomputable section
namespace ActualOriginalAffineInput318
open QuadricCRTAssembly318 ActualOriginalCoordinateFrequency318 MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 16000000

@[expose] def affineInput (f : Coordinates ℝ → ℂ) (c : Coordinates ℝ) (R : ℝ) :
    Coordinates ℝ → ℂ := fun x => f (c+R • x)

lemma actual_affine_input_smooth (f : Coordinates ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (c : Coordinates ℝ) (R : ℝ) : ContDiff ℝ ∞ (affineInput f c R) := by
  exact hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id))

lemma actual_affine_input_compact (f : Coordinates ℝ → ℂ) (hc : HasCompactSupport f)
    (c : Coordinates ℝ) {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (affineInput f c R) := by
  have ht : HasCompactSupport (fun x => f (c+x)) := hc.comp_homeomorph (Homeomorph.addLeft c)
  exact ht.comp_smul hR

lemma actual_original_real_dimension : Module.finrank ℝ (Coordinates ℝ) = 5 := by
  norm_num [Coordinates,Module.finrank_prod]

lemma actual_frequency_smul_left (R : ℝ) (y x : Coordinates ℝ) :
    frequency (R • y) x = R * frequency y x := by
  simp only [actual_frequency_apply,dot,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- Exact affine Jacobian in the unchanged original product volume. -/
lemma actual_original_affine_integral (f : Coordinates ℝ → ℂ) (c : Coordinates ℝ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x : Coordinates ℝ, f (c+R • x)) = (R^5)⁻¹ • ∫ x : Coordinates ℝ, f x := by
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x => f (c+x)) R (hR:=hR.le)]
  rw [actual_original_real_dimension,integral_add_left_eq_self f c]

end ActualOriginalAffineInput318
