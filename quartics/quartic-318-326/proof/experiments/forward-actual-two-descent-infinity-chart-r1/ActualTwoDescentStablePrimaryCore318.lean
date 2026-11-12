module
public import ActualTwoDescentActualShaDualityClassification318
public section
noncomputable section
namespace ActualTwoDescentStablePrimaryCore318
set_option maxHeartbeats 16000000

variable (G : Type*) [CommGroup G]

/-- Canonical subgroup of elements divisible by arbitrarily high powers of two. It is not defined by a finite/infinite branch label. -/
def stableTwoCore : Subgroup G where
  carrier := {x | ∀ k : ℕ, ∃ y : G, y^(2^k)=x}
  one_mem' k := ⟨1,one_pow _⟩
  mul_mem' hx hy k := by
    obtain ⟨a,ha⟩ := hx k
    obtain ⟨b,hb⟩ := hy k
    exact ⟨a*b,by rw [mul_pow,ha,hb]⟩
  inv_mem' hx k := by
    obtain ⟨a,ha⟩ := hx k
    exact ⟨a⁻¹,by rw [inv_pow,ha]⟩

lemma actual_stable_core_mem (x : G) : x ∈ stableTwoCore G ↔ ∀ k : ℕ, ∃ y : G, y^(2^k)=x := Iff.rfl

/-- Every genuine homomorphism carries the canonical stable core into the target stable core. -/
lemma actual_stable_core_functorial {H : Type*} [CommGroup H] (f : G →* H) {x : G}
    (hx : x ∈ stableTwoCore G) : f x ∈ stableTwoCore H := by
  intro k
  obtain ⟨y,hy⟩ := hx k
  exact ⟨f y,by rw [←map_pow,hy]⟩

end ActualTwoDescentStablePrimaryCore318
