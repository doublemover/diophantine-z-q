module
public import ActualTwoDescentFinitePowerLevels318
public section
noncomputable section
namespace ActualTwoDescentFinitePrimaryCyclic318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318
variable (G : Type*) [CommGroup G]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

lemma actual_card_bound_of_annihilator (hfinite : Finite (powerLevel G 1))
    (hcard : Nat.card (powerLevel G 1) ≤ 2) (k : ℕ) (hk : ∀ x : G, x^(2^k)=1) : Nat.card G ≤ 2^k := by
  letI := actual_power_levels_finite G hfinite k
  let f (x : G) : powerLevel G k := ⟨x,hk x⟩
  have hf : Function.Injective f := fun x y h => congrArg Subtype.val h
  exact (Nat.card_le_card_of_injective f hf).trans (actual_power_levels_card G hfinite hcard k)

/-- A finite abelian2-group with at most two2-torsion elements is cyclic. The full group need not be elementary abelian. -/
lemma actual_finite_primary_cyclic [Finite G] (hP : IsPGroup 2 G)
    (hcard : Nat.card (powerLevel G 1) ≤ 2) : IsCyclic G := by
  obtain ⟨k,hk⟩ := (isPGroup_iff_exponent_eq_pow).mp hP
  have hbound : Nat.card G ≤ Monoid.exponent G := by
    rw [hk]
    apply actual_card_bound_of_annihilator G inferInstance hcard k
    intro x
    rw [←hk]
    exact Monoid.pow_exponent_eq_one x
  apply IsCyclic.of_exponent_eq_card
  exact Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos Group.exponent_dvd_nat_card) hbound

end ActualTwoDescentFinitePrimaryCyclic318
