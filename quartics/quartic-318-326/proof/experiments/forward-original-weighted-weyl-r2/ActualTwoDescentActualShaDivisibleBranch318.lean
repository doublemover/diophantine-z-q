module
public import ActualTwoDescentActualShaPrimaryVanishing318
public section
noncomputable section
namespace ActualTwoDescentActualShaDivisibleBranch318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryAlternative318
open ActualTwoDescentActualShaPrimaryVanishing318 ActualTwoDescentActualShaAlternatingQuotient318
open ActualTwoDescentActualShaDefinition318 ActualTwoDescentActualShaRankAlternative318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- Conditional Cassels-Tate algebra with EVERY missing pairing obligation explicit: if the actual finite primary group carries a genuine nondegenerate alternating pairing, the only surviving nonzero branch is infinite2-divisible Sha. -/
theorem actual_sha_primary_zero_or_divisible_from_finite_pairing
    (n : ℚ) (hn : n ≠ 0) (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) {A : Type*} [CommGroup A]
    (hpair : Finite (actualShaPrimary n hn) → ∃ e : actualShaPrimary n hn →* (actualShaPrimary n hn →* A),
      (∀ x, e x x=1) ∧ (∀ x, (∀ y, e x y=1) → x=1)) :
    Subsingleton (actualShaPrimary n hn) ∨
      (Infinite (actualShaPrimary n hn) ∧ Function.Surjective (powMonoidHom (α:=actualShaPrimary n hn) 2)) := by
  rcases actual_sha_primary_finite_or_divisible n hn hf hb hS with ⟨hfin,hcyc⟩|hinf
  · letI := hfin
    obtain ⟨e,he,hnd⟩ := hpair hfin
    exact Or.inl (actual_sha_alternating_finite_quotient_trivial n hn hf hb hS (MonoidHom.id _)
      Function.surjective_id e he hnd)
  · exact Or.inr hinf

end ActualTwoDescentActualShaDivisibleBranch318
