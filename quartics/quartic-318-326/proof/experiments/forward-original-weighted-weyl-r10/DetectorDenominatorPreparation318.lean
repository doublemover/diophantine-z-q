module
public import DetectorPrimeProduct318
public section
noncomputable section
namespace DetectorDenominatorPreparation318
open CircuitReplay ScaledContactWeights318 ScaledDetectorChain318
open DetectorPrimeProduct318
set_option maxHeartbeats 1000000

/-- Outside the support of an integral product every pole valuation is even.
At support primes a nonnegative square factor prevents odd denominator depth. -/
theorem integer_square_denominator (N : ℤ) (z : ℚ) (hN : N≠0) (hz : z≠0)
    (hsupport : ∀ p : ℕ, p.Prime → 0<padicValInt p N → 0≤padicValRat p z) :
    IsSquare (((N:ℚ)*z^2).den) := by
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have hv : padicValRat p ((N:ℚ)*z^2)=
      (padicValInt p N:ℤ)+2*padicValRat p z := by
    rw [padicValRat.mul (by exact_mod_cast hN) (pow_ne_zero _ hz),
      padicValRat.pow,padicValRat.of_int]
    norm_num
  have heven : 0≤padicValRat p ((N:ℚ)*z^2) ∨ Even (padicValRat p ((N:ℚ)*z^2)) := by
    by_cases hpos : 0<padicValInt p N
    · left
      rw [hv]
      have hzv := hsupport p hp hpos
      positivity
    · right
      have hn : padicValInt p N=0 := by omega
      rw [hv,hn,Nat.cast_zero,zero_add]
      exact ⟨padicValRat p z,by ring⟩
  have hd : Even (padicValNat p ((N:ℚ)*z^2).den) := by
    rcases heven with hnonneg|heven
    · rcases Rat.num_or_den_zero_padicVal ((N:ℚ)*z^2) hp with hn|hd
      · have hz : padicValNat p ((N:ℚ)*z^2).den=0 := by
          simp only [padicValRat_def,hn,Nat.cast_zero,zero_sub] at hnonneg
          omega
        simp [hz]
      · simp [hd]
    · exact (Rat.num_den_even_padicVal_of_even_padicVal hp heven).2
  simpa only [Nat.factorization_def _ hp] using hd

lemma squareFactor_value (p : ℕ) [Fact p.Prime] (w : Assignment) (c u d : ℚ)
    (hq : traceQuotient w c (u/d^2)≠0) (hd : d≠0) (hdelta : delta c (u/d^2)≠0) :
    padicValRat p (DetectorPrimeProduct318.squareFactor w c u d)=
      padicValRat p (traceQuotient w c (u/d^2))-
        5*padicValRat p d-3*padicValRat p (delta c (u/d^2)) := by
  rw [DetectorPrimeProduct318.squareFactor,padicValRat.div hq
    (mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hdelta)),
    padicValRat.mul (pow_ne_zero _ hd) (pow_ne_zero _ hdelta),padicValRat.pow,padicValRat.pow]
  norm_num <;> ring

/-- The actual support-unit trace and the selected denominator units give
square reduced denominator for the literal scaled source pole. -/
theorem actual_square_denominator (w : Assignment) (c u d : ℚ)
    (hc : c≠0) (hd : d≠0) (hdelta : delta c (u/d^2)≠0)
    (hq : traceQuotient w c (u/d^2)≠0)
    (k : Fin 5 → ℤ) (hk : ∀ j, linear c u d j=(k j:ℚ)) (hkn : ∀ j, k j≠0)
    (hsupport : ∀ p : ℕ, p.Prime → 0<padicValInt p (product k) →
      padicValRat p (traceQuotient w c (u/d^2))=0 ∧
      padicValRat p d=0 ∧ padicValRat p (delta c (u/d^2))=0) :
    IsSquare (poleInput w c (u/d^2)).den := by
  rw [pole_product w c u d hc hd k hk]
  apply integer_square_denominator (product k) _ (product_ne k hkn)
    (div_ne_zero hq (mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hdelta)))
  intro p hp hs
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hqt,hdt,hdel⟩ := hsupport p hp hs
  change 0 ≤ padicValRat p (DetectorPrimeProduct318.squareFactor w c u d)
  rw [squareFactor_value p w c u d hq hd hdelta,hqt,hdt,hdel]
  norm_num

end DetectorDenominatorPreparation318
