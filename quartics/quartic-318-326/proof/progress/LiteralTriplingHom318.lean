module
public import LiteralSchemePointGroup318
public import Mathlib.Algebra.Group.Subgroup.Ker
public section
noncomputable section
namespace LiteralTriplingHom318
open AlgebraicGeometry CategoryTheory
open LiteralSchemePointOperations318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {T:Scheme}
variable (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))

/-- The actual tripling composite evaluates as scalar multiplication by
three in the already represented group. -/
theorem three_value (p:Points N b) : (3 • p).val=
    p.val ≫ CompletedIteratedAddition318.tripling (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
      (OpenJAffineScheme318.discriminant_unit N) := by
  rw [show (3:ℕ)=2+1 by rfl,add_nsmul,two_nsmul,one_nsmul]
  exact LiteralSchemeCancellation318.triple_value N b p

@[expose] def triplingHom : Points N b →+ Points N b where
  toFun p:=3 • p
  map_zero':=nsmul_zero _
  map_add' p q:=nsmul_add p q 3
/-- Intrinsic three-killed subgroup, before any finite labels are chosen. -/
@[expose] def killed : AddSubgroup (Points N b) := (triplingHom N b).ker
@[simp] theorem mem_killed (p:Points N b) : p∈killed N b ↔ 3 • p=0 := Iff.rfl
end LiteralTriplingHom318
