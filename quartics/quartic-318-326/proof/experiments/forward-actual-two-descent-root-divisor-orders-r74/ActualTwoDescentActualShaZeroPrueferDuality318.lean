module
public import ActualTwoDescentActualShaReducedDuality318
public section
noncomputable section
namespace ActualTwoDescentActualShaZeroPrueferDuality318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaReducedPrimary318
open ActualTwoDescentActualShaReducedDuality318 ActualTwoDescentFinitePrimaryCore318
open ActualTwoDescentActualShaPruefer318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- Global duality, IF actually supplied, removes exactly the reduced finite piece. It still does not choose rational rank one over the Prüfer branch. -/
theorem actual_sha_zero_or_pruefer_of_duality (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    Subsingleton (actualShaPrimary n hn) ∨
      (Infinite (actualShaPrimary n hn) ∧ Nonempty (actualShaPrimary n hn ≃* PrueferTwo)) := by
  by_cases hfin : Finite (actualShaPrimary n hn)
  · letI := hfin
    have he := actual_sha_core_full_of_duality n hn hf hb hS hdual
    change ActualTwoDescentStablePrimaryCore318.stableTwoCore (actualShaPrimary n hn)=⊤ at he
    rw [actual_finite_primary_core_bot _ (actual_sha_primary_is_two_group n hn)] at he
    left
    constructor
    intro x y
    have hx : x=1 := by
      have hm : x ∈ (⊥ : Subgroup (actualShaPrimary n hn)) := by rw [he]; trivial
      exact hm
    have hy : y=1 := by
      have hm : y ∈ (⊥ : Subgroup (actualShaPrimary n hn)) := by rw [he]; trivial
      exact hm
    exact hx.trans hy.symm
  · haveI : Infinite (actualShaPrimary n hn) := not_finite_iff_infinite.mp hfin
    exact Or.inr ⟨inferInstance,actual_infinite_sha_pruefer n hn hf hb hS⟩

end ActualTwoDescentActualShaZeroPrueferDuality318
