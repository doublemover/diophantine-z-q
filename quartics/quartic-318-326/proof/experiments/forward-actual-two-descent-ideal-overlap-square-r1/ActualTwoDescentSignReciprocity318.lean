module
public import ActualTwoDescentSymbolTable318
public section
noncomputable section
namespace ActualTwoDescentSignReciprocity318
open ActualTwoDescentSymbolTable318
set_option maxHeartbeats 16000000

def sign (a : ZMod 2) : ℤ := if a=0 then 1 else -1
lemma sign_zero : sign 0=1 := by norm_num [sign]
lemma sign_one : sign 1= -1 := by norm_num [sign]
lemma sign_add (a b : ZMod 2) : sign (a+b)=sign a*sign b := by
  fin_cases a <;> fin_cases b <;> norm_num [sign]
lemma sign_injective : Function.Injective sign := by
  intro a b h
  fin_cases a <;> fin_cases b <;> norm_num [sign] at h ⊢
lemma sign_natCast (n : ℕ) : sign (n : ZMod 2)=(-1 : ℤ)^n := by
  induction n with
  | zero => simp only [Nat.cast_zero,sign_zero,pow_zero]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,sign_add,ih,sign_one,pow_succ]
lemma actual_sign_symbol (a b : ℕ) (hc : Nat.Coprime a b) :
    sign (symbolBit a b)=jacobiSym (a : ℤ) b := by
  have hg : (a : ℤ).gcd b=1 := by simpa only [Int.gcd_natCast_natCast] using hc
  rcases jacobiSym.eq_one_or_neg_one hg with h | h <;> simp [symbolBit,h,sign]

/-- The actual F2 symbol reciprocity defect, for distinct odd primes.
This is the entrywise arithmetic identity required by the descent matrix. -/
theorem actual_symbol_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hne : p ≠ q) :
    symbolBit p q+symbolBit q p=((p/2 : ℕ) : ZMod 2)*((q/2 : ℕ) : ZMod 2) := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes Fact.out Fact.out).mpr hne
  have hrec : jacobiSym (p : ℤ) q=
      (-1 : ℤ)^(p/2*(q/2))*jacobiSym (q : ℤ) p := by
    rw [←legendreSym.to_jacobiSym,←legendreSym.to_jacobiSym,
      legendreSym.quadratic_reciprocity' hp2 hq2]
  apply sign_injective
  rw [sign_add,actual_sign_symbol p q hc,actual_sign_symbol q p hc.symm,
    ←Nat.cast_mul,sign_natCast,hrec]
  have hg : (q : ℤ).gcd p=1 := by simpa only [Int.gcd_natCast_natCast] using hc.symm
  rcases jacobiSym.eq_one_or_neg_one hg with h | h <;> rw [h] <;> ring

end ActualTwoDescentSignReciprocity318
