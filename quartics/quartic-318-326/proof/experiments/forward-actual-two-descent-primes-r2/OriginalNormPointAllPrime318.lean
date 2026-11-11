module
public import OriginalCompletePrimeRectangle318
public section
noncomputable section
namespace OriginalNormPointAllPrime318
open TernaryQuadraticLineCover318 OriginalEuclideanLattice318 OriginalAnisotropicRectangle318
open OriginalSieveFrame318 OriginalCompletePrimeRectangle318 OriginalNormPointSieveTail318
open OriginalWholeBasisCoordinates318 OriginalAnisotropicResidueFibers318
open OriginalSmallPrimeRectangleTail318
set_option maxHeartbeats 7000000

lemma third_is_shortest {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ι → ℕ} {κ : ℤ} {s : ∀ k, Option (ZMod (q k))} (d : Frame q κ s)
    (R : ℝ) (hR : 0≤R) : d.thirdRadius R≤d.firstRadius R ∧ d.thirdRadius R≤d.secondRadius R := by
  have hU : 0<‖embed d.u‖ := norm_pos_iff.mpr (d.basis.1.2.ne_zero 0)
  have hV := hU.trans_le d.first_second
  have hW := hV.trans_le d.second_third
  have bound (L : ℝ) (hL : 0<L) (hLW : L≤‖embed d.w‖) :
      4*R/‖embed d.w‖≤8*R/L := by
    apply (div_le_div_iff₀ hW hL).mpr
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hLW)]
  exact ⟨floorRadius_mono (bound _ hU (d.first_second.trans d.second_third)),
    floorRadius_mono (bound _ hV d.second_third)⟩

/-- One genuine reciprocal frame of the original retained-prime lattice,
selected BEFORE the point radius, sieve threshold and all witness primes. -/
@[expose] def actualFrame (κ t : ℤ)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k))) : Frame (LiteralSliceModulus318.prime κ t) κ s :=
  Classical.choice (frame_exists (LiteralSliceModulus318.prime κ t)
    (LiteralSliceModulus318.prime_is_prime κ t) κ s)

@[expose] def NormBad (side : Bool) (κ t : ℤ)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k))) (R : ℝ) (Y : ℕ) :=
  {y : NormPoints (LiteralSliceModulus318.prime κ t) κ s R // ∃ p : ℕ,
    p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣t ∧ pointObstruction side κ t y.1.1 p}

/-- The exact original point is encoded in the reciprocal rectangle;
ALL permitted primes are retained on that same point, not just residues. -/
theorem norm_bad_card (side : Bool) (κ t : ℤ)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k)))
    (d : Frame (LiteralSliceModulus318.prime κ t) κ s) (R : ℝ) (hR : 0≤R) (Y : ℕ) :
    Nat.card (NormBad side κ t s R Y)≤
      Nat.card (AllBad side κ t d.u d.v d.z (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) Y) := by
  obtain ⟨f,hf,he⟩ := norm_rectangle_map (LiteralSliceModulus318.prime_is_prime κ t) d R hR
  let g : NormBad side κ t s R Y →
      AllBad side κ t d.u d.v d.z (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) Y := fun y =>
    ⟨f y.1,by
      obtain ⟨p,hp,hY,hκ,ht,ho⟩ := y.2
      exact ⟨p,hp,hY,hκ,ht,by rw [he];exact ho⟩⟩
  have hg : Function.Injective g := fun a b h => Subtype.ext (hf (congrArg Subtype.val h))
  exact Nat.card_le_card_of_injective g hg

@[expose] def pointBudget (κ t : ℤ)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k))) (R : ℝ) (Y : ℕ) : ℝ :=
  let d := actualFrame κ t s
  fullBudget κ t (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) Y ‖embed d.w‖

/-- Complete actual original norm-point geometric prime tail. The caller
supplies neither basis, modulus, local count, finite prime set, eliminant,
height, good leading direction nor zero-locus estimate. All are produced.
This is per original lattice; weighted good-family aggregation is separate. -/
theorem actual_norm_all_prime_tail (side : Bool) (κ t : ℤ) (hκ : κ≠0)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k)))
    (R : ℝ) (hR : 0≤R) (Y : ℕ) (hY : 3≤Y) :
    (Nat.card (NormBad side κ t s R Y):ℝ)*Real.log (Y:ℝ)≤pointBudget κ t s R Y := by
  let d := actualFrame κ t s
  have hc : (Nat.card (NormBad side κ t s R Y):ℝ)≤
      (Nat.card (AllBad side κ t d.u d.v d.z (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) Y):ℝ) := by
    exact_mod_cast norm_bad_card side κ t s d R hR Y
  have hs := third_is_shortest d R hR
  have hh := complete_rectangle_tail side κ t hκ s d.u d.v d.w d.z d.basis
    d.first_second d.second_third d.last_bound _ _ _ Y hY hs.1 hs.2
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  exact (mul_le_mul_of_nonneg_right hc hl).trans hh

end OriginalNormPointAllPrime318
