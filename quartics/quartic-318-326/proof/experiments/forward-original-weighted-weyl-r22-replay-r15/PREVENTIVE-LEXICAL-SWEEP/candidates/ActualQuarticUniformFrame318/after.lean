module
public import ActualQuarticGoodFamily318
public section
noncomputable section
namespace ActualQuarticUniformFrame318
open TernaryQuadraticLineCover318 OriginalEuclideanLattice318 OriginalSieveFrame318
open OriginalUniformGoodGeometry318 OriginalUniformGoodHeight318
open ActualQuarticCompletePrimeRectangle318 ActualQuarticNormAllPrime318
open ActualQuarticCoefficientHeight318 ActualQuarticUniformHeight318
open OriginalUniformEliminantHeight318 OriginalReducedRectangleVolume318 OriginalShearBoxBudget318
open OriginalCommonGoodCutoff318 OriginalThirdMinimumTail318
open OriginalNormPointAllPrime318 (actualFrame)
set_option maxHeartbeats 11000000

lemma coefficient_mono (κ t : ℤ) (L H : ℝ) (hL : 0≤L) (hLH : L≤H) :
    coefficientHeight κ t L≤coefficientHeight κ t H := by
  have h2 := pow_le_pow_left₀ hL hLH 2
  have hJ : innerHeight κ t L≤ innerHeight κ t H := by
    dsimp [innerHeight]
    nlinarith [mul_le_mul_of_nonneg_left h2 (show 0≤2*|(κ:ℝ)|+2 by positivity)]
  have hJ0 : 0≤ innerHeight κ t L := by dsimp [innerHeight];positivity
  have hJ2 := pow_le_pow_left₀ hJ0 hJ 2
  have ht2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (t:ℝ))
  have hQ : quarticHeight κ t L≤quarticHeight κ t H := by dsimp [quarticHeight];linarith
  have hF : formHeight κ t L≤formHeight κ t H := by
    exact add_le_add_right (mul_le_mul_of_nonneg_left h2 (by positivity)) _
  dsimp [coefficientHeight]
  linarith

@[expose] def globalHeight (κ t : ℤ) (R : ℝ) : ℝ :=
  1+(49*R)^2*pointHeight κ t (58*R^2)
lemma global_one (κ t : ℤ) (R : ℝ) : 1≤globalHeight κ t R := by
  have hp := point_nonneg κ t (58*R^2)
  dsimp [globalHeight]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hp)

/-- Explicit same-index all-prime budget for the ACTUAL second Gaussian
source. The improved factor2 support bound gives240100 on its area term;
zero-cylinder constant352800 retains every actual t=-2 fiber. -/
@[expose] def uniformBudget (κ t : ℤ) (R T : ℝ) (Y : ℕ) : ℝ :=
  (262144*R^3/(Y:ℝ))*Real.log (Y:ℝ)+
    240100*R^2*T*Real.log (globalHeight κ t R)+352800*R^2*T*Real.log (Y:ℝ)

variable (κ t : ℤ)
  (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
    Option (ZMod (LiteralSliceModulus318.prime κ t k)))
  (d : Frame (LiteralSliceModulus318.prime κ t) κ s)

/-- Uniform polynomial height of every actual enlarged rectangle, from
integrality U>=1 and original reciprocal widths. Only the logarithmic
height is enlarged; actual area and cylinder geometry are kept separate. -/
lemma frame_height (R : ℝ) (hWR : ‖embed d.w‖≤R) :
    fullHeight κ t (d.firstRadius R+4*d.thirdRadius R) (d.secondRadius R+4*d.thirdRadius R)
      (heightRadius (d.firstRadius R+4*d.thirdRadius R)
        (d.secondRadius R+4*d.thirdRadius R) ‖embed d.w‖)≤globalHeight κ t R := by
  let A := d.firstRadius R+4*d.thirdRadius R
  let B := d.secondRadius R+4*d.thirdRadius R
  let L := heightRadius A B ‖embed d.w‖
  have hL : 0≤L := by dsimp [L,heightRadius];positivity
  have hLH : L≤58*R^2 := height_radius_bound κ t s d R hWR
  have hU := first_norm_one κ t s d
  have hV := hU.trans d.first_second
  obtain ⟨ha,hb,hc⟩ := enlarged_scaled κ t s d R hWR
  change (2*(A:ℝ)+1)*‖embed d.u‖≤49*R at ha
  change (2*(B:ℝ)+1)*‖embed d.v‖≤49*R at hb
  have ha0 : 0≤2*(A:ℝ)+1 := by positivity
  have hb0 : 0≤2*(B:ℝ)+1 := by positivity
  have ha' : 2*(A:ℝ)+1≤49*R := by
    have h := mul_le_mul_of_nonneg_left hU ha0
    nlinarith only [ha,h]
  have hb' : 2*(B:ℝ)+1≤49*R := by
    have h := mul_le_mul_of_nonneg_left hV hb0
    nlinarith only [hb,h]
  have hR : 0≤49*R := ha0.trans ha'
  have harea : (2*(A:ℝ)+1)*(2*(B:ℝ)+1)≤(49*R)^2 := by
    simpa only [pow_two] using mul_le_mul ha' hb' hb0 hR
  have hcoef := coefficient_mono κ t L (58*R^2) hL hLH
  have hpow := pow_le_pow_left₀ (coefficient_nonneg κ t L) hcoef 9
  have hpoint : pointHeight κ t L≤pointHeight κ t (58*R^2) :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hh := mul_le_mul harea hpoint (point_nonneg κ t L) (sq_nonneg (49*R))
  change fullHeight κ t A B L≤globalHeight κ t R
  dsimp [fullHeight,globalHeight]
  push_cast
  linarith only [hh]

/-- Entire explicit per-frame all-prime budget times the ORIGINAL index
is uniform over every good lattice. Small-prime source volume and all
large-prime area/zero-cylinder terms are consumed at their actual indices. -/
theorem frame_budget (R T : ℝ) (hWR : ‖embed d.w‖≤R) (hWT : ‖embed d.w‖≤T)
    (Y : ℕ) (hY : 3≤Y) :
    fullBudget κ t (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) Y ‖embed d.w‖ *
      (LiteralSliceModulus318.modulus κ t:ℝ)^2≤uniformBudget κ t R T Y := by
  let A := d.firstRadius R
  let B := d.secondRadius R
  let C := d.thirdRadius R
  let a : ℝ := 2*((A:ℝ)+4*(C:ℝ))+1
  let b : ℝ := 2*((B:ℝ)+4*(C:ℝ))+1
  let c : ℝ := 2*(C:ℝ)+1
  let m : ℝ := (LiteralSliceModulus318.modulus κ t:ℝ)^2
  let N := fullHeight κ t (A+4*C) (B+4*C) (heightRadius (A+4*C) (B+4*C) ‖embed d.w‖)
  have hm : 0≤m := sq_nonneg _
  have hR : 0≤R := (norm_nonneg _).trans hWR
  have hT : 0≤T := (norm_nonneg _).trans hWT
  have hYR : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  have hN1 : 1≤N := full_one κ t (A+4*C) (B+4*C) _
  have hlogN := Real.log_nonneg hN1
  have hlog := Real.log_le_log (zero_lt_one.trans_le hN1) (frame_height κ t s d R hWR)
  have hlogG := Real.log_nonneg (global_one κ t R)
  obtain ⟨harea,hzero⟩ := original_area_cylinder κ t s d R T hWR hWT
  have hvol := actual_rectangle_volume (LiteralSliceModulus318.prime κ t)
    (LiteralSliceModulus318.prime_is_prime κ t) (LiteralSliceModulus318.prime_injective κ t)
    (LiteralSliceModulus318.prime_odd κ t) κ s d.u d.v d.w d.z d.basis
    d.first_second d.second_third d.last_bound R hR
  change ((A*B*C:ℕ):ℝ)*m≤512*R^3 at hvol
  push_cast at harea hzero
  change a*b*m≤4802*R^2*T at harea
  change (a+b)*c*m≤1764*R^2*T at hzero
  change Real.log N≤Real.log (globalHeight κ t R) at hlog
  have hareaLog := mul_le_mul harea hlog hlogN (by positivity : 0≤4802*R^2*T)
  have hzeroLog := mul_le_mul_of_nonneg_right hzero hl
  have hsmall : (512*(A:ℝ)*(B:ℝ)*(C:ℝ)/(Y:ℝ))*m≤262144*R^3/(Y:ℝ) := by
    apply (le_div_iff₀ hYR).mpr
    have he : (512*(A:ℝ)*(B:ℝ)*(C:ℝ)/(Y:ℝ))*m*(Y:ℝ)=512*((A*B*C:ℕ):ℝ)*m := by
      push_cast
      field_simp [ne_of_gt hYR]
      <;> ring
    rw [he]
    nlinarith only [hvol]
  have hsmallLog := mul_le_mul_of_nonneg_right hsmall hl
  change fullBudget κ t A B C Y ‖embed d.w‖*m≤_
  dsimp only [fullBudget,largeBudget,uniformBudget]
  push_cast
  change ((512*(A:ℝ)*(B:ℝ)*(C:ℝ)/(Y:ℝ))*Real.log (Y:ℝ)+
    25*(a*b*2*Real.log N+8*(a+b)*c*Real.log (Y:ℝ)))*m≤_
  nlinarith only [hsmallLog,hareaLog,hzeroLog]

/-- SAME bad-tail complement supplies W<=T, with T<=R. The actual
frame was selected earlier independently of radius and primes. -/
theorem good_point_budget (R T : ℝ) (hTR : T≤R) (Y : ℕ) (hY : 3≤Y)
    (hgood : ¬LargeThird (LiteralSliceModulus318.prime κ t) κ s T) :
    pointBudget κ t s R Y*(LiteralSliceModulus318.modulus κ t:ℝ)^2≤uniformBudget κ t R T Y := by
  let d := actualFrame κ t s
  have hWT := good_third_bound κ t s d T hgood
  exact frame_budget κ t s d R T (hWT.trans hTR) hWT Y hY

end ActualQuarticUniformFrame318
