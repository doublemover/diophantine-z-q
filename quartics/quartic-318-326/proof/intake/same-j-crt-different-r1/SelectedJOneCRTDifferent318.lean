module
public import SelectedJOneDirectLenstraClear318
public import SelectedJOneCRTTrace318

public section
noncomputable section

namespace SelectedJOneCRTDifferent318

open UniqueFactorizationMonoid
open SelectedJOneDirectLenstraClear318 (exponent multiplier padic_lt_exponent natCast_pow_not_dvd)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Clear the actual different of the uncompleted finite free Dedekind algebra.
The prime-power branch and its complement come from factorization of the mapped
multiplier ideal, rather than a decomposition after completing the base. -/
theorem multiplier_mem_different {A B : Type*}
    [CommRing A] [IsDedekindDomain A] [IsLocalRing A] [CharZero A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B]
    [Module.Free A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (p M : ℕ) [Fact p.Prime] (hp : ¬ IsUnit (↑p : A))
    (hM : M ≠ 0) (hpM : p ∣ M) (hdegree : Module.finrank A B ≤ M ^ 2) :
    (↑(multiplier M) : B) ∈ differentIdeal A B := by
  classical
  let I : Ideal A := Ideal.span {(↑(multiplier M) : A)}
  let J : Ideal B := I.map (algebraMap A B)
  let D : Ideal B := differentIdeal A B
  have hI0 : I ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr (pow_ne_zero _ hM))
  have hJ0 : J ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hI0
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨v, hv⟩ := pow_dvd_pow_of_dvd hpM (exponent M)
  have hpN : (↑p : A) ^ exponent M ∣ (↑(multiplier M) : A) := by
    refine ⟨(↑v : A), ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow] using congrArg (fun n : ℕ => (↑n : A)) hv
  have hnot {r : ℕ} (hr : 0 < r) (hrank : r ≤ M ^ 2) : (↑r : A) ∉ I := by
    intro h
    exact natCast_pow_not_dvd A hp hr.ne' (padic_lt_exponent hr hrank)
      (hpN.trans (Ideal.mem_span_singleton.mp h))
  have hI : I ≠ ⊤ := by
    intro h
    have hM2 : 1 ≤ M ^ 2 :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero (pow_ne_zero 2 hM))
    apply hnot Nat.one_pos hM2
    rw [h]
    trivial
  have hbranch (P : Ideal B) [P.IsMaximal] :
      ¬ P ^ Multiset.count P (normalizedFactors J) ∣ D := by
    have hPmax : (P.under A).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    have hJP : J ≤ P := by
      apply Ideal.map_le_iff_le_comap.mpr
      change I ≤ P.under A
      rw [IsLocalRing.eq_maximalIdeal hPmax]
      exact IsLocalRing.le_maximalIdeal hI
    have hPmem : P ∈ normalizedFactors J := (Ideal.mem_normalizedFactors_iff hJ0).mpr
      ⟨(inferInstance : P.IsMaximal).isPrime, hJP⟩
    have hPcount : 0 < Multiset.count P (normalizedFactors J) :=
      Multiset.count_pos.mpr hPmem
    obtain ⟨Q, hcop, hprod⟩ := Ideal.eq_prime_pow_mul_coprime hJ0 P
    have hpowP : P ^ Multiset.count P (normalizedFactors J) ≤ P := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hPcount.ne'
      rw [hk, pow_succ]
      exact Ideal.mul_le_right
    have hproper : P ^ Multiset.count P (normalizedFactors J) ≠ ⊤ := by
      intro h
      rw [h] at hpowP
      exact (inferInstance : P.IsMaximal).ne_top (top_le_iff.mp hpowP)
    have hcopPow : IsCoprime (P ^ Multiset.count P (normalizedFactors J)) Q :=
      (Ideal.isCoprime_iff_sup_eq.mpr hcop).pow_left
    obtain ⟨c, hc, _, r, hr, hrd, htrace⟩ := SelectedJOneCRTTrace318.exists_selected_trace
      I (P ^ Multiset.count P (normalizedFactors J)) Q hI hproper hcopPow hprod.symm
    have hint : Algebra.intTrace A B c ∉ I := by
      rw [Algebra.intTrace_eq_trace]
      intro hcI
      apply hnot hr (hrd.trans hdegree)
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_natCast, ← htrace]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hcI
    exact not_dvd_differentIdeal_of_intTrace_notMem A _ Q hprod.symm c hc hint
  have hDJ : D ∣ J := by
    apply (dvd_iff_normalizedFactors_le_normalizedFactors hD0 hJ0).mpr
    apply Multiset.le_iff_count.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors D
    · have hprime : Prime P := prime_of_normalized_factor P hP
      have : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
      by_contra h
      obtain ⟨Q, _, hprod⟩ := Ideal.eq_prime_pow_mul_coprime hD0 P
      have hdiv : P ^ Multiset.count P (normalizedFactors D) ∣ D := ⟨Q, hprod⟩
      exact hbranch P ((pow_dvd_pow P (le_of_lt (lt_of_not_ge h))).trans hdiv)
    · rw [Multiset.count_eq_zero.mpr hP]
      exact Nat.zero_le _
  apply (Ideal.dvd_iff_le.mp hDJ)
  change (↑(multiplier M) : B) ∈ I.map (algebraMap A B)
  rw [← map_natCast (algebraMap A B) (multiplier M)]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)

end SelectedJOneCRTDifferent318

#print axioms SelectedJOneCRTDifferent318.multiplier_mem_different
