module
public import OriginalUniformGoodGeometry318
public section
noncomputable section
namespace OriginalUniformGoodHeight318
open TernaryQuadraticLineCover318 OriginalEuclideanLattice318 OriginalSieveFrame318
open OriginalFullEuclideanLattice318 OriginalUniformGoodGeometry318
open OriginalUniformEliminantHeight318 OriginalShearBoxBudget318 OriginalAffineRectangleTail318
set_option maxHeartbeats 7000000

lemma bothHeight_mono (κ t : ℤ) (L H : ℝ) (hL : 0≤L) (hLH : L≤H) :
    bothHeight κ t L≤bothHeight κ t H := by
  have h2 := pow_le_pow_left₀ hL hLH 2
  have h4 := pow_le_pow_left₀ hL hLH 4
  have hf : formHeight κ t L≤formHeight κ t H := by
    exact add_le_add_right (mul_le_mul_of_nonneg_left h2 (by positivity)) _
  have hn : factorHeight t L≤factorHeight t H := by
    exact add_le_add_right (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤2)) _
  have hf0 : 0≤formHeight κ t L := by dsimp [formHeight];positivity
  have hn0 : 0≤factorHeight t L := by dsimp [factorHeight];positivity
  have hf2 := pow_le_pow_left₀ hf0 hf 2
  have hn2 := pow_le_pow_left₀ hn0 hn 2
  have hm := mul_le_mul hf2 hn2 (sq_nonneg _) (sq_nonneg _)
  have hreg : regularHeight κ t L≤regularHeight κ t H := by
    dsimp [regularHeight]
    nlinarith only [hm]
  have ht := mul_le_mul_of_nonneg_left h2 (sq_nonneg (t:ℝ))
  have hex : exceptionalHeight t L≤exceptionalHeight t H := by
    dsimp [exceptionalHeight]
    nlinarith only [h4,ht]
  dsimp [bothHeight]
  linarith

variable (κ t : ℤ)
  (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
    Option (ZMod (LiteralSliceModulus318.prime κ t k)))
  (d : Frame (LiteralSliceModulus318.prime κ t) κ s)

lemma first_norm_one : 1≤‖embed d.u‖ := by
  apply le_of_not_gt
  intro hh
  have hu := embed_zero_of_norm_lt_one d.u hh
  have hz : embed d.u=0 := by simp [hu,embed]
  exact d.basis.1.2.ne_zero 0 hz

/-- Uniform original eliminant height radius. Integrality supplies U>=1,
while the actual short-radius product C*W<=4R prevents an extra factor of
W on the shear correction. The result is polynomial in ORIGINAL radius. -/
theorem height_radius_bound (R : ℝ) (hWR : ‖embed d.w‖≤R) :
    heightRadius (d.firstRadius R+4*d.thirdRadius R)
      (d.secondRadius R+4*d.thirdRadius R) ‖embed d.w‖≤58*R^2 := by
  have hU := first_norm_one κ t s d
  have hV := hU.trans d.first_second
  have hW := hV.trans d.second_third
  have hR1 := hW.trans hWR
  have hR : 0≤R := by linarith
  obtain ⟨hA,hB,hC⟩ := radius_scaled κ t s d R hR
  have hA0 : 0≤(d.firstRadius R:ℝ) := by positivity
  have hB0 : 0≤(d.secondRadius R:ℝ) := by positivity
  have hAu := mul_le_mul_of_nonneg_left hU hA0
  have hBv := mul_le_mul_of_nonneg_left hV hB0
  have hAA : (d.firstRadius R:ℝ)≤8*R := by nlinarith only [hA,hAu]
  have hBB : (d.secondRadius R:ℝ)≤8*R := by nlinarith only [hB,hBv]
  have hAW := mul_le_mul hAA hWR (norm_nonneg _) (by positivity : 0≤8*R)
  have hBW := mul_le_mul hBB hWR (norm_nonneg _) (by positivity : 0≤8*R)
  dsimp [heightRadius]
  push_cast
  nlinarith only [hAW,hBW,hC,hWR,mul_nonneg hR (sub_nonneg.mpr hR1)]

@[expose] def globalHeight (κ t : ℤ) (R : ℝ) : ℝ := bothHeight κ t (58*R^2)

lemma globalHeight_one (R : ℝ) : 1≤globalHeight κ t R := by
  dsimp [globalHeight,bothHeight,regularHeight,exceptionalHeight]
  positivity

/-- The SAME original actual eliminant-height logarithm is controlled by
a bound independent of the individual good lattice and its basis. -/
theorem actual_log_height (R : ℝ) (hWR : ‖embed d.w‖≤R) :
    Real.log (bothHeight κ t (heightRadius (d.firstRadius R+4*d.thirdRadius R)
      (d.secondRadius R+4*d.thirdRadius R) ‖embed d.w‖))≤Real.log (globalHeight κ t R) := by
  apply Real.log_le_log
  · have h1 : 1≤bothHeight κ t (heightRadius (d.firstRadius R+4*d.thirdRadius R)
        (d.secondRadius R+4*d.thirdRadius R) ‖embed d.w‖) := by
      dsimp [bothHeight,regularHeight,exceptionalHeight]
      positivity
    linarith
  · exact bothHeight_mono κ t _ _ (by dsimp [heightRadius];positivity)
      (height_radius_bound κ t s d R hWR)

end OriginalUniformGoodHeight318
