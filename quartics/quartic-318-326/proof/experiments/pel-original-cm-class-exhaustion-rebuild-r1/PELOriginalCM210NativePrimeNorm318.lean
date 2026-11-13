module
public import PELOriginalCM210NativePrimeResidue318
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public section
noncomputable section
namespace PELOriginalCM210NativePrimeNorm318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210NativePrimeResidue318
variable (p:ℕ) (hp:(p:ℤ)∣210) [NeZero p]
lemma native_norm : Ideal.absNorm (nativeIdeal p hp)=p := by
  change Nat.card (O⧸nativeIdeal p hp)=p
  rw [Nat.card_congr (nativeQuotientEquiv p hp).toEquiv,Nat.card_eq_fintype_card,ZMod.card]
lemma native_nonzero : nativeIdeal p hp≠⊥ := by
  intro h
  have hn := native_norm p hp
  rw [h,Ideal.absNorm_bot] at hn
  exact (NeZero.ne p) hn.symm
lemma native_prime (hprime:p.Prime) : (nativeIdeal p hp).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [native_norm]
  exact (Nat.irreducible_iff_nat_prime _).mpr hprime
end PELOriginalCM210NativePrimeNorm318
