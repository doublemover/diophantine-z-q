module
public import ActualQuarticCompletePrimeRectangle318
public section
noncomputable section
namespace ActualQuarticNormAllPrime318
open TernaryQuadraticLineCover318 OriginalEuclideanLattice318 OriginalAnisotropicRectangle318
open OriginalSieveFrame318 ActualQuarticCompletePrimeRectangle318 OriginalNormPointSieveTail318
open OriginalWholeBasisCoordinates318 OriginalAnisotropicResidueFibers318
open ActualGaussianIntegerFibers318 ActualGaussianChartObstruction318
open OriginalNormPointAllPrime318 (actualFrame third_is_shortest)
set_option maxHeartbeats 7000000

@[expose] def NormBad (κ t : ℤ)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k))) (R : ℝ) (Y : ℕ) :=
  {y : NormPoints (LiteralSliceModulus318.prime κ t) κ s R // ∃ p : ℕ,
    p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣t ∧ Obstruction true κ t y.1.1 p}

/-- The exact original point is encoded in the reciprocal rectangle;
ALL permitted primes are retained on that same point, not just residues. -/
theorem norm_bad_card (κ t : ℤ)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k)))
    (d : Frame (LiteralSliceModulus318.prime κ t) κ s) (R : ℝ) (hR : 0≤R) (Y : ℕ) :
    Nat.card (NormBad κ t s R Y)≤
      Nat.card (AllBad κ t d.u d.v d.z (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) Y) := by
  obtain ⟨f,hf,he⟩ := norm_rectangle_map (LiteralSliceModulus318.prime_is_prime κ t) d R hR
  let g : NormBad κ t s R Y →
      AllBad κ t d.u d.v d.z (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) Y := fun y =>
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
theorem actual_norm_all_prime_tail (κ t : ℤ) (hκ : κ≠0) (ht0 : t≠0)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k)))
    (R : ℝ) (hR : 0≤R) (Y : ℕ) (hY : 3≤Y) :
    (Nat.card (NormBad κ t s R Y):ℝ)*Real.log (Y:ℝ)≤pointBudget κ t s R Y := by
  let d := actualFrame κ t s
  have hc : (Nat.card (NormBad κ t s R Y):ℝ)≤
      (Nat.card (AllBad κ t d.u d.v d.z (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) Y):ℝ) := by
    exact_mod_cast norm_bad_card κ t s d R hR Y
  have hs := third_is_shortest d R hR
  have hh := complete_rectangle_tail κ t hκ ht0 s d.u d.v d.w d.z d.basis
    d.first_second d.second_third d.last_bound _ _ _ Y hY hs.1 hs.2
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  exact (mul_le_mul_of_nonneg_right hc hl).trans hh

end ActualQuarticNormAllPrime318
