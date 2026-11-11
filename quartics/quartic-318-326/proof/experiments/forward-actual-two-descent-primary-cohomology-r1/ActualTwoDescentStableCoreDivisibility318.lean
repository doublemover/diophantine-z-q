module
public import ActualTwoDescentStableCoreMaximality318
public section
noncomputable section
namespace ActualTwoDescentStableCoreDivisibility318
set_option maxHeartbeats 16000000

open ActualTwoDescentStablePrimaryCore318 ActualTwoDescentFinitePrimaryCore318 ActualTwoDescentInfinitePrimaryCore318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentInfinitePrimaryDivisible318
open ActualTwoDescentPrimaryAllRoots318 ActualTwoDescentStableCoreMaximality318
variable (G : Type*) [CommGroup G]

lemma actual_stable_core_primary (hP : IsPGroup 2 G) : IsPGroup 2 (stableTwoCore G) := by
  intro x
  obtain ⟨k,hk⟩ := hP x.val
  exact ⟨k,Subtype.ext hk⟩

lemma actual_stable_core_square_surjective (hP : IsPGroup 2 G)
    (ht : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2) :
    Function.Surjective (powMonoidHom (α:=stableTwoCore G) 2) := by
  by_cases hf : Finite G
  · letI := hf
    intro x
    have hx : x=1 := Subtype.ext (by
      have h := x.property
      rw [actual_finite_primary_core_bot G hP] at h
      exact h)
    exact ⟨1,by simpa only [map_one] using hx.symm⟩
  · haveI : Infinite G := not_finite_iff_infinite.mp hf
    intro x
    obtain ⟨y,hy⟩ := actual_infinite_primary_square_surjective G hP ht hc x.val
    have hmem : y ∈ stableTwoCore G := by rw [actual_infinite_primary_core_top G hP ht hc]; trivial
    exact ⟨⟨y,hmem⟩,Subtype.ext hy⟩

/-- The canonical core is genuinely divisible, and contains every divisible subgroup. -/
theorem actual_maximal_divisible_primary_core (hP : IsPGroup 2 G)
    (ht : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2) :
    (∀ m : ℕ, m ≠ 0 → Function.Surjective (fun x : stableTwoCore G => x^m)) ∧
    ∀ H : Subgroup G, (∀ m : ℕ, m ≠ 0 → Function.Surjective (fun x : H => x^m)) → H ≤ stableTwoCore G := by
  constructor
  · intro m hm
    exact actual_primary_all_power_surjective (actual_stable_core_primary G hP)
      (actual_stable_core_square_surjective G hP ht hc) hm
  · intro H hH
    exact actual_square_divisible_subgroup_le_core G H (hH 2 (by decide))

end ActualTwoDescentStableCoreDivisibility318
