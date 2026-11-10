module
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic
public section
namespace RegularLeftModuleAutomorphisms318
set_option maxHeartbeats 900000
variable (R : Type*) [Ring R]

/-- Full additive automorphisms commuting with ALL left regular multipliers. -/
abbrev Automorphisms := {f : R ≃+ R // ∀ a b : R, f (a*b)=a*f b}

@[expose] def rightUnit (u : Rˣ) : R ≃+ R where
  toFun x := x*(u:R)
  invFun x := x*(↑u⁻¹:R)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_add' x y := add_mul x y u

theorem rightUnit_commutes (u : Rˣ) (a b : R) : rightUnit R u (a*b)=a*rightUnit R u b :=
  mul_assoc _ _ _

theorem regular_value (f : Automorphisms R) (x : R) : f.val x=x*f.val 1 := by
  simpa only [mul_one] using f.property x 1

/-- The multiplier is extracted from the actual automorphism value at1.
Its inverse uses the actual inverse automorphism, so no finiteness is needed. -/
@[expose] def multiplier (f : Automorphisms R) : Rˣ where
  val := f.val 1
  inv := f.val.symm 1
  val_inv := by
    apply f.val.injective
    rw [f.property,AddEquiv.apply_symm_apply,mul_one]
  inv_val := by
    rw [← regular_value R f]
    exact f.val.apply_symm_apply 1

@[expose] def unitsEquiv : Rˣ ≃ Automorphisms R where
  toFun u := ⟨rightUnit R u,rightUnit_commutes R u⟩
  invFun := multiplier R
  left_inv u := by apply Units.ext; change 1*(u:R)=(u:R); exact one_mul _
  right_inv f := by
    apply Subtype.ext
    apply AddEquiv.ext
    intro x
    exact (regular_value R f x).symm

/-- Composition order is explicitly retained: right multiplication is an
opposite action, not an accidental left-action homomorphism. -/
theorem rightUnit_product (u v : Rˣ) :
    rightUnit R (u*v)=(rightUnit R u).trans (rightUnit R v) := by
  apply AddEquiv.ext
  intro x
  exact (mul_assoc x (u:R) (v:R)).symm
end RegularLeftModuleAutomorphisms318
