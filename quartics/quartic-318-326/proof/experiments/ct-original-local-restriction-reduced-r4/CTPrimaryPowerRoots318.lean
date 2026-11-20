module
public import Mathlib.Algebra.Group.Subgroup.Defs
public section

namespace PrimaryDivisibleIntersection318

variable {G K : Type*} [Group G] [Group K]

/-- The literal subgroup divisibility predicate used by the native stable
core. Only positive powers are tested. -/
def HasPowerRoots (D : Subgroup G) : Prop :=
  ∀ m : ℕ, m ≠ 0 → Function.Surjective (fun x : D => x ^ m)

end PrimaryDivisibleIntersection318
