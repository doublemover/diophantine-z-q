module
public import ActualOriginalAffineInput318
public section
noncomputable section
namespace ActualOriginalAffineFourier318
open QuadricCRTAssembly318 ActualOriginalCoordinateFrequency318 ActualOriginalCompactFourier318
open ActualOriginalAffineInput318 MeasureTheory
set_option maxHeartbeats 16000000

lemma actual_affine_fourier_phase (c y x : Coordinates ℝ) {R : ℝ} (hR : R ≠ 0) :
    Real.fourierChar (-frequency y x) =
      Real.fourierChar (frequency (R⁻¹ • y) c) *
        Real.fourierChar (-frequency (R⁻¹ • y) (c+R • x)) := by
  rw [←AddChar.map_add_eq_mul]
  congr 1
  simp only [map_add,map_smul,smul_eq_mul,actual_frequency_smul_left]
  field_simp [hR]
  <;> ring

/-- The actual full Fourier transform of a shifted/dilated compact input.
The positive translation character, inverse scale in frequency and rank-five
Jacobian are all derived in the original norm and Haar product. -/
theorem actual_original_affine_fourier (f : Coordinates ℝ → ℂ) (c y : Coordinates ℝ)
    {R : ℝ} (hR : 0 < R) :
    compactFourier (affineInput f c R) y =
      (Real.fourierChar (frequency (R⁻¹ • y) c) : ℂ) *
        ((R^5)⁻¹ • compactFourier f (R⁻¹ • y)) := by
  let H : Coordinates ℝ → ℂ := fun x => Real.fourierChar (-frequency (R⁻¹ • y) x) • f x
  calc
    compactFourier (affineInput f c R) y =
        ∫ x : Coordinates ℝ, (Real.fourierChar (frequency (R⁻¹ • y) c) : ℂ) * H (c+R • x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change Real.fourierChar (-frequency y x) • f (c+R • x) = _
      rw [actual_affine_fourier_phase c y x hR.ne']
      simp only [H,Circle.smul_def,Circle.coe_mul,smul_eq_mul,mul_assoc]
    _ = (Real.fourierChar (frequency (R⁻¹ • y) c) : ℂ) *
        (∫ x : Coordinates ℝ, H (c+R • x)) := integral_const_mul _ _
    _ = (Real.fourierChar (frequency (R⁻¹ • y) c) : ℂ) *
        ((R^5)⁻¹ • compactFourier f (R⁻¹ • y)) := by
      rw [actual_original_affine_integral H c hR]
      rfl

end ActualOriginalAffineFourier318
