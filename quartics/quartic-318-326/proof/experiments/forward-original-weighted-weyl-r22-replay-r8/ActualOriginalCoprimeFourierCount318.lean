module
public import ActualOriginalProductQuadric318
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
namespace ActualOriginalCoprimeFourierCount318
open QuadricCRTAssembly318 ActualOriginalProductQuadric318
open ActualOriginalCompleteFourierCount318
set_option maxHeartbeats 16000000

/-- Exact CRT for the original quadric at arbitrary coprime moduli,
not only a squarefree product of distinct primes. -/
@[expose] def originalCoprimeEquiv (κ : ℤ) (a b : ℕ) (hab : a.Coprime b) :
    Quadric (κ : ZMod (a*b)) ≃ Quadric (κ : ZMod a) × Quadric (κ : ZMod b) :=
  (quadricRingEquiv (ZMod.chineseRemainder hab) (κ : ZMod (a*b))
    ((κ : ZMod a),(κ : ZMod b)) (by simp)).trans
      (productQuadricEquiv (κ : ZMod a) (κ : ZMod b))

theorem actual_original_coprime_count (κ : ℤ) (a b : ℕ) (hab : a.Coprime b) :
    Nat.card (Quadric (κ : ZMod (a*b))) =
      Nat.card (Quadric (κ : ZMod a)) * Nat.card (Quadric (κ : ZMod b)) := by
  rw [Nat.card_congr (originalCoprimeEquiv κ a b hab),Nat.card_prod]

/-- The actual q^-5 COMPLETE-frequency average is multiplicative on
coprime nonzero moduli, through the exact original solution-count CRT.
This does not assert multiplicativity of primitive-frequency coefficients. -/
theorem actual_complete_average_coprime (κ : ℤ) (a b : ℕ)
    [NeZero a] [NeZero b] (hab : a.Coprime b) :
    completeAverage κ (a*b) = completeAverage κ a * completeAverage κ b := by
  rw [actual_complete_average_count,actual_complete_average_count,
    actual_complete_average_count,actual_original_coprime_count κ a b hab]
  push_cast
  rw [mul_pow,mul_div_mul_comm]

end ActualOriginalCoprimeFourierCount318
