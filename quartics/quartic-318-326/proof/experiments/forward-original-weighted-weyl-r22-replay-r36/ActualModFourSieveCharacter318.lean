module
public import ActualSelbergRemainderBudget318
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public section
noncomputable section
namespace ActualModFourSieveCharacter318
open scoped BigOperators
open ZMod
set_option maxHeartbeats 16000000

/-- The genuine level-four Dirichlet character, not an independently
postulated function on primes. -/
@[expose] def complexCharacter : DirichletCharacter ℂ 4 :=
  χ₄.ringHomComp (Int.castRingHom ℂ)
@[expose] def realCharacter (n : ℕ) : ℝ := (χ₄ (n:ZMod 4):ℤ)
lemma complex_character_value (n : ℕ) :
    complexCharacter (n:ZMod 4)=(realCharacter n:ℂ) := by
  simp only [complexCharacter,MulChar.ringHomComp_apply,Int.castRingHom_apply,realCharacter,
    Complex.ofReal_intCast]
lemma character_at_three : complexCharacter (3:ZMod 4)= -1 := by
  change ((-1:ℤ):ℂ)= -1
  norm_num
lemma character_nontrivial : complexCharacter≠1 := by
  intro he
  have hh := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3:ZMod 4)) he
  rw [character_at_three,MulChar.one_apply (by decide : IsUnit (3:ZMod 4))] at hh
  norm_num at hh

/-- The EXACT quadratic-character sign appearing in the original
finite-field density is the value of this same Dirichlet character. -/
theorem original_prime_character (p : ℕ) [Fact p.Prime] (hp2 : p≠2) :
    (quadraticChar (ZMod p) (-1:ZMod p):ℝ)=realCharacter p := by
  have hh := legendreSym.at_neg_one hp2
  have hi : quadraticChar (ZMod p) (-1:ZMod p)=χ₄ (p:ZMod 4) := by
    simpa only [legendreSym,Int.cast_neg,Int.cast_one] using hh
  simpa only [realCharacter] using congrArg (fun z : ℤ => (z:ℝ)) hi

lemma real_character_le_one (p : ℕ) : realCharacter p≤1 := by
  have hh := isQuadratic_χ₄ (p:ZMod 4)
  rcases hh with h|h|h <;> simp only [realCharacter,h] <;> norm_num

/-- Genuine nonvanishing at the boundary for this ACTUAL source character,
using Mathlib's proved Dirichlet theorem, not a one-shot external port. -/
theorem original_character_L_nonzero : DirichletCharacter.LFunction complexCharacter 1≠0 :=
  complexCharacter.LFunction_ne_zero_of_re_eq_one (by simp) (Or.inl character_nontrivial)

end ActualModFourSieveCharacter318
