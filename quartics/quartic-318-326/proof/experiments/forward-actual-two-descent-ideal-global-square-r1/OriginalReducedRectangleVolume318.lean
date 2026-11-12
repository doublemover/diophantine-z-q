module
public import OriginalSmallPrimeRectangleTail318
public section
noncomputable section
namespace OriginalReducedRectangleVolume318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalThirdMinimumTail318 OriginalBasisDeterminantIndex318
open OriginalGoodLatticeVolumeBound318 OriginalAnisotropicResidueFibers318 OriginalSmallPrimeRectangleTail318
set_option maxHeartbeats 4000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Volume of the actual reciprocal-minimum coefficient rectangle, with
integer floors retained, compared to the ORIGINAL exact index M². -/
theorem actual_rectangle_volume (q : ι → ℕ) (hq : ∀ i, (q i).Prime)
    (hd : Function.Injective q) (hp2 : ∀ i, q i≠2) (κ : ℤ)
    (s : ∀ i, Option (ZMod (q i))) (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (R : ℝ) (hR : 0≤R) :
    ((floorRadius (8*R/‖embed u‖)*floorRadius (8*R/‖embed v‖)*
      floorRadius (4*R/‖embed w‖):ℕ):ℝ)*(FixedSquarefreeCRT318.modulus q:ℝ)^2≤512*R^3 := by
  have hU : 0<‖embed u‖ := norm_pos_iff.mpr (hb.1.2.ne_zero 0)
  have hV : 0<‖embed v‖ := hU.trans_le huv
  have hW : 0<‖embed w‖ := hV.trans_le hvw
  let A := floorRadius (8*R/‖embed u‖)
  let B := floorRadius (8*R/‖embed v‖)
  let C := floorRadius (4*R/‖embed w‖)
  have hA : (A:ℝ)*‖embed u‖≤8*R := (le_div_iff₀ hU).mp (floorRadius_le _ (by positivity))
  have hB : (B:ℝ)*‖embed v‖≤8*R := (le_div_iff₀ hV).mp (floorRadius_le _ (by positivity))
  have hC : (C:ℝ)*‖embed w‖≤4*R := (le_div_iff₀ hW).mp (floorRadius_le _ (by positivity))
  have hprod := mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hC (by positivity) (by positivity)
  have hm : (FixedSquarefreeCRT318.modulus q:ℝ)^2≤2*(‖embed u‖*‖embed v‖*‖embed w‖) := by
    rw [←actual_basis_determinant_index q hq hd hp2 κ s u v z hb]
    exact actual_determinant_upper u v w z hz
  have hh := mul_le_mul_of_nonneg_left hm (show 0≤((A*B*C:ℕ):ℝ) by positivity)
  change ((A*B*C:ℕ):ℝ)*(FixedSquarefreeCRT318.modulus q:ℝ)^2≤512*R^3
  push_cast at hh ⊢
  nlinarith only [hprod,hh]

/-- An actual low-prime coefficient-obstruction mass bound measured in
original source-volume units: count*M²*Y<=110592R³. All local arithmetic,
finite union, cutoff sum, rectangle shape and exact index are constructed. -/
theorem actual_volume_small_prime_tail (side : Bool) (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ label) κ s u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (R : ℝ) (hR : 0≤R)
    (Y : ℕ) (hY : 0<Y) (S : Finset ℕ)
    (hprime : ∀ p∈S, p.Prime) (hκ : ∀ p∈S, ¬(p:ℤ)∣κ)
    (ht : ∀ p∈S, ¬(p:ℤ)∣label) (hcut : ∀ p∈S, Y<p)
    (hsize : ∀ p∈S, p≤floorRadius (8*R/‖embed u‖) ∧
      p≤floorRadius (8*R/‖embed v‖) ∧ p≤floorRadius (4*R/‖embed w‖)) :
    (Nat.card {c : Rectangle (floorRadius (8*R/‖embed u‖))
        (floorRadius (8*R/‖embed v‖)) (floorRadius (4*R/‖embed w‖)) //
      ∃ p : ↥S, integerObstruction side κ label u v z (coordinates c) p.1}:ℝ)*
      (LiteralSliceModulus318.modulus κ label:ℝ)^2*(Y:ℝ)≤110592*R^3 := by
  let A := floorRadius (8*R/‖embed u‖)
  let B := floorRadius (8*R/‖embed v‖)
  let C := floorRadius (4*R/‖embed w‖)
  have hc := actual_small_prime_tail side κ label s u v z hb A B C Y hY S hprime hκ ht hcut hsize
  have hYR : (0:ℝ)<Y := by exact_mod_cast hY
  have hc' := (le_div_iff₀ hYR).mp hc
  have hvol := actual_rectangle_volume (LiteralSliceModulus318.prime κ label)
    (LiteralSliceModulus318.prime_is_prime κ label) (LiteralSliceModulus318.prime_injective κ label)
    (LiteralSliceModulus318.prime_odd κ label) κ s u v w z hb huv hvw hz R hR
  have hh := mul_le_mul_of_nonneg_right hc' (sq_nonneg (LiteralSliceModulus318.modulus κ label:ℝ))
  change ((A*B*C:ℕ):ℝ)*(LiteralSliceModulus318.modulus κ label:ℝ)^2≤512*R^3 at hvol
  push_cast at hvol
  nlinarith only [hh,hvol]

end OriginalReducedRectangleVolume318
