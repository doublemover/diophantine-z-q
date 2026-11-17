module
public import ActualTwoDescentActualShaPruefer318
public section
noncomputable section
namespace ActualTwoDescentActualShaPrimaryClassification318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryAlternative318
open ActualTwoDescentActualShaPruefer318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Complete ACTUAL rank-one primary classification: one finite cyclic2-power group OR the explicit dyadic Prüfer group. No global duality theorem has selected a branch. -/
theorem actual_sha_primary_classification (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    (∃ k : ℕ, Nonempty (actualShaPrimary n hn ≃* Multiplicative (ZMod (2^k)))) ∨
      Nonempty (actualShaPrimary n hn ≃* PrueferTwo) := by
  rcases actual_sha_primary_finite_or_divisible n hn hf hb hS with ⟨hfin,hcyc⟩|⟨hinf,_⟩
  · letI := hfin
    letI := hcyc
    obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp (actual_sha_primary_is_two_group n hn)
    left
    refine ⟨k,?_⟩
    have e := zmodCyclicMulEquiv hcyc
    rw [hk] at e
    exact ⟨e.symm⟩
  · letI := hinf
    exact Or.inr (actual_infinite_sha_pruefer n hn hf hb hS)

end ActualTwoDescentActualShaPrimaryClassification318
