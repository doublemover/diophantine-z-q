module
public import ActualTwoDescentPrescribedPrime318
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public section
noncomputable section
namespace ActualTwoDescentReciprocalPrime318
open ActualTwoDescentResidueBits318 ActualTwoDescentPrescribedPrime318
set_option maxHeartbeats 16000000

/-- The original one-way symbol prescription produces the reverse
symbols by ACTUAL quadratic reciprocity. This is not an independent choice
of both directions; the precise parity correction is retained. -/
theorem actual_reciprocal_prescribed_prime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hcop : ∀ i, Nat.Coprime (p i) 12) (hp2 : ∀ i, p i ≠ 2)
    (bits : ι → Bool) (special : Bool) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ q : ℕ, ∃ hprime : q.Prime, N < q ∧ 2 < q ∧ q ∉ forbidden ∧
      (∀ i, q ≠ p i) ∧ (q : ZMod 12)=(if special then 7 else 1) ∧
      (∀ i, quadraticChar (ZMod (p i)) (q : ZMod (p i))=bitSign (bits i)) ∧
      (letI : Fact q.Prime := ⟨hprime⟩
       ∀ i, legendreSym q (p i : ℤ)=
         (-1 : ℤ)^((p i)/2*(q/2))*bitSign (bits i)) := by
  obtain ⟨q,hq,hprime,hforbid,hfresh,htype,hbits⟩ :=
    actual_prescribed_prime p hd hcop hp2 bits special forbidden (max N 2)
  letI : Fact q.Prime := ⟨hprime⟩
  have hq2 : 2 < q := lt_of_le_of_lt (le_max_right _ _) hq
  refine ⟨q,hprime,lt_of_le_of_lt (le_max_left _ _) hq,hq2,hforbid,hfresh,htype,hbits,?_⟩
  intro i
  have hf : legendreSym (p i) (q : ℤ)=bitSign (bits i) := by
    simpa only [legendreSym,Int.cast_natCast] using hbits i
  rw [legendreSym.quadratic_reciprocity' (hp2 i) (by omega : q ≠ 2),hf]

end ActualTwoDescentReciprocalPrime318
