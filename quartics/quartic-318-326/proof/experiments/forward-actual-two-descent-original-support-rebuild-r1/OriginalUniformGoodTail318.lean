module
public import OriginalUniformGoodHeight318
public section
noncomputable section
namespace OriginalUniformGoodTail318
open TernaryQuadraticLineCover318 OriginalEuclideanLattice318 OriginalSieveFrame318
open OriginalCompletePrimeRectangle318 OriginalNormPointAllPrime318
open OriginalUniformGoodGeometry318 OriginalUniformGoodHeight318
open OriginalReducedRectangleVolume318 OriginalAffineRectangleTail318 OriginalShearBoxBudget318
open OriginalCommonGoodCutoff318 OriginalThirdMinimumTail318
set_option maxHeartbeats 8500000

/-- Explicit index-normalized uniform geometric budget. The R²T term is
obtained from the ACTUAL three minima and original determinant, not from
an assumed generic short basis. -/
@[expose] def uniformBudget (κ t : ℤ) (R T : ℝ) (Y : ℕ) : ℝ :=
  (262144*R^3/(Y:ℝ))*Real.log (Y:ℝ)+
    480200*R^2*T*Real.log (globalHeight κ t R)+352800*R^2*T*Real.log (Y:ℝ)

variable (κ t : ℤ)
  (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
    Option (ZMod (LiteralSliceModulus318.prime κ t k)))
  (d : Frame (LiteralSliceModulus318.prime κ t) κ s)

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
  let N := bothHeight κ t (heightRadius (A+4*C) (B+4*C) ‖embed d.w‖)
  have hm : 0≤m := sq_nonneg _
  have hR : 0≤R := (norm_nonneg _).trans hWR
  have hT : 0≤T := (norm_nonneg _).trans hWT
  have hYR : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  have hN1 : 1≤N := by dsimp [N,bothHeight,OriginalUniformEliminantHeight318.regularHeight,
    OriginalUniformEliminantHeight318.exceptionalHeight];positivity
  have hlogN := Real.log_nonneg hN1
  have hlog := actual_log_height κ t s d R hWR
  have hlogG := Real.log_nonneg (globalHeight_one κ t R)
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
    25*(a*b*4*Real.log N+8*(a+b)*c*Real.log (Y:ℝ)))*m≤_
  nlinarith only [hsmallLog,hareaLog,hzeroLog]

/-- SAME bad-tail complement supplies W<=T, with T<=R. The actual
frame was selected earlier independently of radius and primes. -/
theorem good_point_budget (R T : ℝ) (hTR : T≤R) (Y : ℕ) (hY : 3≤Y)
    (hgood : ¬LargeThird (LiteralSliceModulus318.prime κ t) κ s T) :
    pointBudget κ t s R Y*(LiteralSliceModulus318.modulus κ t:ℝ)^2≤uniformBudget κ t R T Y := by
  let d := actualFrame κ t s
  have hWT := good_third_bound κ t s d T hgood
  exact frame_budget κ t s d R T (hWT.trans hTR) hWT Y hY

end OriginalUniformGoodTail318
