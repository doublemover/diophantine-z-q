module
public import ActualTwoDescentSelmerCharacterFreeRankOne318
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Topology.Algebra.PontryaginDual
public section
noncomputable section
namespace ActualTwoDescentCirclePrimaryInvolutions318
set_option maxHeartbeats 16000000
open ActualTwoDescentPrimaryPowerLevels318

abbrev CirclePrimary := CommGroup.primaryComponent Circle 2
abbrev CircleInvolutions := {z : Circle // z^2=1}

lemma actual_circle_involution_unique (x y : Circle) (hx : x^2=1) (hy : y^2=1)
    (hx0 : x ≠ 1) (hy0 : y ≠ 1) : x=y := by
  have hxC : (x : ℂ)^2=1 := congrArg (fun z : Circle => (z : ℂ)) hx
  have hyC : (y : ℂ)^2=1 := congrArg (fun z : Circle => (z : ℂ)) hy
  have hx1 : (x : ℂ) ≠ 1 := fun h => hx0 (Subtype.ext h)
  have hy1 : (y : ℂ) ≠ 1 := fun h => hy0 (Subtype.ext h)
  apply Subtype.ext
  exact ((sq_eq_one_iff.mp hxC).resolve_left hx1).trans ((sq_eq_one_iff.mp hyC).resolve_left hy1).symm

lemma actual_circle_involutions_finite_card : Finite CircleInvolutions ∧ Nat.card CircleInvolutions ≤ 2 := by
  classical
  let f (x : CircleInvolutions) : Bool := decide (x.val=1)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    by_cases hx : x.val=1
    · have hy : y.val=1 := by by_contra hy; simp [f,hx,hy] at h
      exact hx.trans hy.symm
    · have hy : y.val ≠ 1 := by intro hy; simp [f,hx,hy] at h
      exact actual_circle_involution_unique _ _ x.property y.property hx hy
  haveI : Finite CircleInvolutions := Finite.of_injective f hf
  exact ⟨inferInstance,by simpa using Nat.card_le_card_of_injective f hf⟩

def circlePrimaryTwoInclusion : powerLevel CirclePrimary 1 → CircleInvolutions :=
  fun x => ⟨x.val.val,by
    have h := congrArg Subtype.val x.property
    simpa only [pow_one] using h⟩

lemma actual_circle_primary_two_bound :
    Finite (powerLevel CirclePrimary 1) ∧ Nat.card (powerLevel CirclePrimary 1) ≤ 2 := by
  obtain ⟨hf,hc⟩ := actual_circle_involutions_finite_card
  letI := hf
  have hi : Function.Injective circlePrimaryTwoInclusion := by
    intro x y h
    apply Subtype.ext; apply Subtype.ext
    exact congrArg Subtype.val h
  exact ⟨Finite.of_injective circlePrimaryTwoInclusion hi,
    (Nat.card_le_card_of_injective circlePrimaryTwoInclusion hi).trans hc⟩

end ActualTwoDescentCirclePrimaryInvolutions318
