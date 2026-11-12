module
public import ActualOriginalAffinePoisson318
public section
noncomputable section
namespace ActualOriginalResiduePoisson318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCoordinateFrequency318
open ActualOriginalTwistedWeight318 ActualOriginalCompactFourier318
open ActualOriginalAffineInput318 ActualOriginalAffineFourier318 ActualOriginalAffinePoisson318
open scoped ContDiff
set_option maxHeartbeats 16000000

lemma actual_equation_smul (κ R : ℝ) (x : Coordinates ℝ) :
    equation κ (R • x) = R^2 * equation κ x := by
  simp only [equation,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

@[expose] def scaledOriginalWeight (κ β B : ℝ) (W : Coordinates ℝ → ℝ)
    (x : Coordinates ℝ) : ℂ :=
  (W (B⁻¹ • x) : ℂ) * Complex.exp ((2*Real.pi*β*equation κ x : ℝ)*Complex.I)

lemma actual_scaled_twisted_identity (κ β B : ℝ) (hB : B ≠ 0)
    (W : Coordinates ℝ → ℝ) (x : Coordinates ℝ) :
    twistedWeight κ (β*B^2) W (B⁻¹ • x) = scaledOriginalWeight κ β B W x := by
  have hp : 2*Real.pi*(β*B^2)*equation κ (B⁻¹ • x) =
      2*Real.pi*β*equation κ x := by
    rw [actual_equation_smul]
    field_simp [hB]
    <;> ring
  unfold twistedWeight scaledOriginalWeight
  rw [hp]

lemma actual_residue_affine_input (q B : ℝ) (r x : Coordinates ℝ) :
    B⁻¹ • r+(q/B) • x = B⁻¹ • (r+q • x) := by
  rw [smul_add,smul_smul]
  simp only [div_eq_mul_inv]
  congr 1
  congr 1
  ring

lemma actual_residue_frequency (q B : ℝ) (hq : q ≠ 0) (hB : B ≠ 0)
    (m r : Coordinates ℝ) :
    frequency ((q/B)⁻¹ • m) (B⁻¹ • r) = frequency m r / q := by
  rw [actual_frequency_smul_left,map_smul]
  simp only [smul_eq_mul]
  field_simp [hq,hB]
  <;> ring

/-- Exact Poisson for one actual residue-parameter sum. The source is
W((r+q*z)/B) times the original beta quadratic phase. The produced dual has
Jacobian (B/q)^5, positive residue character and beta*B^2 oscillatory integral.
No unit-frequency or rational-arc averaging is silently inserted. -/
theorem actual_original_residue_poisson (κ β : ℝ) (q : ℕ) (hq : 0 < q)
    (B : ℝ) (hB : 0 < B) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (r : Coordinates ℤ) :
    (∑' z : Coordinates ℤ, scaledOriginalWeight κ β B W
      (integerEmbed r+(q : ℝ) • integerEmbed z)) =
      ∑' m : Coordinates ℤ,
        (Real.fourierChar (frequency (integerEmbed m) (integerEmbed r)/(q : ℝ)) : ℂ) *
          ((B/(q : ℝ))^5 • originalCoordinateFourier κ (β*B^2) W
            ((B/(q : ℝ)) • integerEmbed m)) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hs := actual_original_affine_poisson (twistedWeight κ (β*B^2) W)
    (actual_twisted_weight_smooth κ (β*B^2) W hW)
    (actual_twisted_weight_compact κ (β*B^2) W hWc)
    (B⁻¹ • integerEmbed r) (R:=(q : ℝ)/B) (div_pos hqr hB)
  simp_rw [actual_residue_affine_input,actual_scaled_twisted_identity κ β B hB.ne' W] at hs
  rw [hs]
  apply tsum_congr
  intro m
  rw [actual_residue_frequency (q : ℝ) B hqr.ne' hB.ne']
  simp only [inv_pow,inv_div]
  rfl

end ActualOriginalResiduePoisson318
