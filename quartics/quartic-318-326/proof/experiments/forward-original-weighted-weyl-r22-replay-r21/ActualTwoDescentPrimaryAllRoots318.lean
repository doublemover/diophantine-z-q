module
public import ActualTwoDescentActualShaDivisibleBranch318
public import Mathlib.GroupTheory.Divisible
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.Category.Grp.Injective
public section
noncomputable section
namespace ActualTwoDescentPrimaryAllRoots318
set_option maxHeartbeats 16000000

open ActualTwoDescentCompatiblePrimaryHalves318
variable {G : Type*} [CommGroup G]

/-- Genuine2-divisibility of a2-primary group implies divisibility by EVERY nonzero natural integer. -/
lemma actual_primary_all_power_surjective (hP : IsPGroup 2 G)
    (hs : Function.Surjective (powMonoidHom (α:=G) 2)) {m : ℕ} (hm : m ≠ 0) :
    Function.Surjective (fun x : G => x^m) := by
  obtain ⟨k,a,ha,rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  intro x
  obtain ⟨y,hy⟩ := (hP.powEquiv (Nat.coprime_two_left.mpr ha)).surjective x
  refine ⟨halfTower hs y k,?_⟩
  rw [pow_mul,actual_half_tower_power]
  exact hy

def primaryRootable (hP : IsPGroup 2 G) (hs : Function.Surjective (powMonoidHom (α:=G) 2)) : RootableBy G ℕ :=
  rootableByOfPowLeftSurj G ℕ (fun hm => actual_primary_all_power_surjective hP hs hm)

def primaryAdditiveDivisible (hP : IsPGroup 2 G) (hs : Function.Surjective (powMonoidHom (α:=G) 2)) : DivisibleBy (Additive G) ℕ :=
  divisibleByOfSMulRightSurj (Additive G) ℕ (fun hm x => by
    obtain ⟨y,hy⟩ := actual_primary_all_power_surjective hP hs hm x.toMul
    exact ⟨Additive.ofMul y,congrArg Additive.ofMul hy⟩)

end ActualTwoDescentPrimaryAllRoots318
