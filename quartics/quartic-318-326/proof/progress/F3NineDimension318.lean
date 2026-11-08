module
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public section
noncomputable section
namespace F3NineDimension318
variable (V : Type*) [AddCommGroup V] [Module (ZMod 3) V]
/-- Finiteness follows from the actual positive cardinal; it is not supplied as an assumption. -/
theorem finite (h : Nat.card V = 9) : Finite V :=
  Nat.finite_of_card_ne_zero (h ▸ by decide)
/-- A genuine F3 module with nine elements has dimension two. -/
theorem finrank_two (h : Nat.card V = 9) : Module.finrank (ZMod 3) V = 2 := by
  letI : Finite V := finite V h
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
  apply Nat.pow_right_injective (a := 3) (by decide)
  simpa [h] using hc.symm
end F3NineDimension318
