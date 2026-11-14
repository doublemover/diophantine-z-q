module
public import ActualQuarticFiniteShearCover318
public section
noncomputable section
namespace ActualQuarticCompletePrimeRectangle318
open scoped BigOperators
open TernaryQuadraticLineCover318 OriginalControlledIntegralBasis318
open OriginalAnisotropicResidueFibers318 ActualGaussianIntegerFibers318
open OriginalCommonGoodCutoff318 OriginalNormPointSieveTail318 OriginalWholeBasisCoordinates318
open ActualQuarticFiniteShearCover318 ActualQuarticRectangleTail318 OriginalShearBoxBudget318
open ActualGaussianSmallPrimeTail318 OriginalEuclideanLattice318
open ActualGaussianChartObstruction318 ActualQuarticUniformHeight318
set_option maxHeartbeats 9000000

/-- ALL permitted original primes above Y, with no upper cutoff, no
chosen prime set, no leading-prime exclusions and no omitted middle band. -/
@[expose] def AllBad (κ t : ℤ) (u v z : Vector ℤ) (A B C Y : ℕ) :=
  {c : Rectangle A B C // ∃ p : ℕ, p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣t ∧
    Obstruction true κ t (synthesis u v z (coordinates c)) p}
@[expose] def SmallBad (κ t : ℤ) (u v z : Vector ℤ) (A B C Y : ℕ) :=
  {c : Rectangle A B C // ∃ p : ↥(smallPrimes κ t Y (2*C)),
    integerActual true κ t u v z (coordinates c) p.1}

/-- An actual partition at the SAME full short width2C. The retained
modulus exclusion follows from its original divisibility into t. Primes2
and3 lie below the explicitly required Y>=3, not in an unproved exception. -/
theorem actual_prime_split (κ t : ℤ) (u v z : Vector ℤ)
    (A B C Y : ℕ) (hY : 3≤Y) :
    Nat.card (AllBad κ t u v z A B C Y)≤
      Nat.card (SmallBad κ t u v z A B C Y)+
        Nat.card (OriginalBad κ t u v z (LiteralSliceModulus318.modulus κ t) A B C Y) := by
  classical
  let Target := SmallBad κ t u v z A B C Y ⊕
    OriginalBad κ t u v z (LiteralSliceModulus318.modulus κ t) A B C Y
  let forget : Target → Rectangle A B C := Sum.elim Subtype.val Subtype.val
  have cover (c : AllBad κ t u v z A B C Y) : ∃ x : Target, forget x=c.1 := by
    obtain ⟨p,hp,hYp,hκ,ht,ho⟩ := c.2
    by_cases hsmall : p≤2*C
    · refine ⟨Sum.inl ⟨c.1,⟨⟨p,(mem_smallPrimes κ t Y (2*C) p).mpr
        ⟨hp,hκ,ht,hYp,hsmall⟩⟩,ho⟩⟩,rfl⟩
    · have h5 : 5≤p := by
        by_contra hh
        have he : p=4 := by omega
        rw [he] at hp
        norm_num at hp
      have hM : ¬(p:ℤ)∣(LiteralSliceModulus318.modulus κ t:ℤ) := fun h =>
        ht (dvd_trans h (LiteralSliceModulus318.modulus_divides_label κ t))
      exact ⟨Sum.inr ⟨c.1,p,hp,h5,hYp,by omega,hκ,hM,ho⟩,rfl⟩
  let f := fun c => Classical.choose (cover c)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact (Classical.choose_spec (cover a)).symm.trans
      ((congrArg forget he).trans (Classical.choose_spec (cover b)))
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Target,Nat.card_eq_fintype_card,Fintype.card_sum] using hh

@[expose] def largeBudget (κ t : ℤ) (A B C Y : ℕ) (W : ℝ) : ℝ :=
  let A' := A+4*C
  let B' := B+4*C
  let N := fullHeight κ t A' B' (heightRadius A' B' W)
  25*(((2*A'+1:ℕ):ℝ)*(2*B'+1)*2*Real.log N+
    8*((2*A'+1:ℕ)+(2*B'+1):ℝ)*(2*C+1)*Real.log (Y:ℝ))
@[expose] def fullBudget (κ t : ℤ) (A B C Y : ℕ) (W : ℝ) : ℝ :=
  (512*(A:ℝ)*(B:ℝ)*(C:ℝ)/(Y:ℝ))*Real.log (Y:ℝ)+largeBudget κ t A B C Y W

/-- Complete ACTUAL second Gaussian Pprime/K per-lattice coefficient rectangle tail. Small, middle and large prime ranges join with no gap.
No basis, modulus, leading coefficient or eliminant-height replacements. -/
theorem complete_rectangle_tail (κ t : ℤ) (hκ : κ≠0) (ht0 : t≠0)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k))) (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ t) κ s u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (A B C Y : ℕ) (hY : 3≤Y)
    (hCA : C≤A) (hCB : C≤B) :
    (Nat.card (AllBad κ t u v z A B C Y):ℝ)*Real.log (Y:ℝ)≤
      fullBudget κ t A B C Y ‖embed w‖ := by
  have hc : (Nat.card (AllBad κ t u v z A B C Y):ℝ)≤
      (Nat.card (SmallBad κ t u v z A B C Y):ℝ)+
      (Nat.card (OriginalBad κ t u v z (LiteralSliceModulus318.modulus κ t) A B C Y):ℝ) := by
    exact_mod_cast actual_prime_split κ t u v z A B C Y hY
  have hs := actual_small_prime_tail true κ t s u v z hb A B C Y (by omega)
    (smallPrimes κ t Y (2*C))
    (fun p hp => ((mem_smallPrimes _ _ _ _ _).mp hp).1)
    (fun p hp => ((mem_smallPrimes _ _ _ _ _).mp hp).2.1)
    (fun p hp => ((mem_smallPrimes _ _ _ _ _).mp hp).2.2.1)
    (fun p hp => ((mem_smallPrimes _ _ _ _ _).mp hp).2.2.2.1) (by
      intro p hp
      have hh := ((mem_smallPrimes _ _ _ _ _).mp hp).2.2.2.2
      exact ⟨hh.trans (by omega),hh.trans (by omega),hh⟩)
  have hb' := actual_large_prime_rectangle κ t hκ ht0 s u v w z hb huv hvw hz A B C Y (by omega)
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  have h0 := mul_le_mul_of_nonneg_right hc hl
  have h1 := mul_le_mul_of_nonneg_right hs hl
  change _≤largeBudget κ t A B C Y ‖embed w‖ at hb'
  change _≤fullBudget κ t A B C Y ‖embed w‖
  dsimp only [fullBudget]
  change (Nat.card (SmallBad κ t u v z A B C Y):ℝ)*_≤_ at h1
  nlinarith only [h0,h1,hb']

end ActualQuarticCompletePrimeRectangle318
