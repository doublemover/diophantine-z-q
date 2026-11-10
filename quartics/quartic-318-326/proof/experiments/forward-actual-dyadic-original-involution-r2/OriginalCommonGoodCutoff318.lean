module
public import OriginalNormPointSieveTail318
public section
noncomputable section
namespace OriginalCommonGoodCutoff318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalAnisotropicRectangle318 OriginalSieveFrame318 OriginalNormPointSieveTail318
open OriginalThreeDimensionalTransference318 OriginalThirdMinimumTail318
open OriginalReciprocalMinimaRectangle318 OriginalGoodMinimumConsumer318
set_option maxHeartbeats 5000000

/-- The literal finite prime range, independent of a basis or individual
lattice. It contains every permitted prime between the two cutoffs. -/
@[expose] def smallPrimes (κ label : ℤ) (Y H : ℕ) : Finset ℕ :=
  (Finset.range (H+1)).filter (fun p => p.Prime ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣label ∧ Y<p)

lemma mem_smallPrimes (κ label : ℤ) (Y H p : ℕ) :
    p∈smallPrimes κ label Y H ↔ p.Prime ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣label ∧ Y<p ∧ p≤H := by
  simp only [smallPrimes,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hpH,hp,hκ,ht,hy⟩
    exact ⟨hp,hκ,ht,hy,by omega⟩
  · rintro ⟨hp,hκ,ht,hy,hpH⟩
    exact ⟨by omega,hp,hκ,ht,hy⟩

lemma good_third_bound (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (d : Frame (LiteralSliceModulus318.prime κ label) κ s) (T : ℝ)
    (hgood : ¬LargeThird (LiteralSliceModulus318.prime κ label) κ s T) : ‖embed d.w‖≤T := by
  classical
  unfold LargeThird at hgood
  push_neg at hgood
  obtain ⟨f,hf,hfT⟩ := hgood
  obtain ⟨i,hiout⟩ := independent_outside_plane _ κ s d.u d.v f hf
  exact (d.third_minimal (f i) (hf.1 i) hiout).trans (hfT i)

/-- A common threshold from the same good-lattice condition fits EVERY
actual anisotropic side. Thus primes can be chosen before the lattice. -/
lemma common_cutoff (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (d : Frame (LiteralSliceModulus318.prime κ label) κ s)
    (T R : ℝ) (hR : 0≤R)
    (hgood : ¬LargeThird (LiteralSliceModulus318.prime κ label) κ s T) :
    floorRadius (4*R/T)≤d.firstRadius R ∧
    floorRadius (4*R/T)≤d.secondRadius R ∧ floorRadius (4*R/T)≤d.thirdRadius R := by
  have hU : 0<‖embed d.u‖ := norm_pos_iff.mpr (d.basis.1.2.ne_zero 0)
  have hV := hU.trans_le d.first_second
  have hW := hV.trans_le d.second_third
  have hWT := good_third_bound κ label s d T hgood
  have hT := hW.trans_le hWT
  have huT := d.first_second.trans (d.second_third.trans hWT)
  have hvT := d.second_third.trans hWT
  have bound (L : ℝ) (hL : 0<L) (hLT : L≤T) : 4*R/T≤8*R/L := by
    apply (div_le_div_iff₀ hT hL).mpr
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hLT)]
  refine ⟨floorRadius_mono (bound _ hU huT),floorRadius_mono (bound _ hV hvT),?_⟩
  exact floorRadius_mono (div_le_div_of_nonneg_left (by positivity) hW hWT)

/-- Complete original norm-point consumer for all primes in a COMMON
range. Neither a basis, a local count, a prime set nor a sieve tail is
supplied by the caller. The good predicate is exactly the old bad-tail complement. -/
theorem actual_common_good_tail (side : Bool) (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (T R : ℝ) (hR : 0≤R) (Y : ℕ) (hY : 0<Y)
    (hgood : ¬LargeThird (LiteralSliceModulus318.prime κ label) κ s T) :
    (Nat.card {y : NormPoints (LiteralSliceModulus318.prime κ label) κ s R //
      ∃ p : ↥(smallPrimes κ label Y (floorRadius (4*R/T))),
        pointObstruction side κ label y.1.1 p.1}:ℝ)*
      (LiteralSliceModulus318.modulus κ label:ℝ)^2*(Y:ℝ)≤110592*R^3 := by
  obtain ⟨d⟩ := frame_exists (LiteralSliceModulus318.prime κ label)
    (LiteralSliceModulus318.prime_is_prime κ label) κ s
  have hs := common_cutoff κ label s d T R hR hgood
  apply actual_norm_point_tail side κ label s d R hR Y hY _
  · intro p hp; exact ((mem_smallPrimes _ _ _ _ _).mp hp).1
  · intro p hp; exact ((mem_smallPrimes _ _ _ _ _).mp hp).2.1
  · intro p hp; exact ((mem_smallPrimes _ _ _ _ _).mp hp).2.2.1
  · intro p hp; exact ((mem_smallPrimes _ _ _ _ _).mp hp).2.2.2.1
  · intro p hp
    have hh := ((mem_smallPrimes _ _ _ _ _).mp hp).2.2.2.2
    exact ⟨hh.trans hs.1,hh.trans hs.2.1,hh.trans hs.2.2⟩

end OriginalCommonGoodCutoff318
