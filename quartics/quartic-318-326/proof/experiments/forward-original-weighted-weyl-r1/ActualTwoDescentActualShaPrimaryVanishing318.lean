module
public import ActualTwoDescentPrimaryTrivialityCriterion318
public section
noncomputable section
namespace ActualTwoDescentActualShaPrimaryVanishing318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaDefinition318 ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryTwo318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentPrimaryTrivialityCriterion318

lemma actual_sha_primary_trivial_of_sha_two_one (n : ℚ) (hn : n ≠ 0)
    (h : Nat.card (actualShaTwo n hn)=1) : Subsingleton (actualShaPrimary n hn) := by
  haveI : Subsingleton (actualShaTwo n hn) := (Nat.card_eq_one_iff_unique.mp h).1
  have ht : Subsingleton (powerLevel (actualShaPrimary n hn) 1) :=
    ⟨fun x y => (primaryShaTwoEquiv n hn).injective (Subsingleton.elim _ _)⟩
  exact actual_primary_trivial_of_two_trivial (actual_sha_primary_is_two_group n hn) ht

lemma actual_sha_two_one_of_primary_trivial (n : ℚ) (hn : n ≠ 0)
    (h : Subsingleton (actualShaPrimary n hn)) : Nat.card (actualShaTwo n hn)=1 := by
  letI := h
  haveI : Subsingleton (actualShaTwo n hn) := ⟨by
    intro x y
    obtain ⟨a,rfl⟩ := (primaryShaTwoEquiv n hn).surjective x
    obtain ⟨b,rfl⟩ := (primaryShaTwoEquiv n hn).surjective y
    exact congrArg (primaryShaTwoEquiv n hn) (Subsingleton.elim a b)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩

end ActualTwoDescentActualShaPrimaryVanishing318
