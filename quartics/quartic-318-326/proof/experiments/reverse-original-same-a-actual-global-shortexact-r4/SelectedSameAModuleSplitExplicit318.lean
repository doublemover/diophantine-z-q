module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Make the affine retraction split its very row

An exact and surjective pair of actual module maps, with its specified
first retraction, gives a splitting. The lift is explicitly corrected
by subtracting its component on the given first summand.
-/

public section

open CategoryTheory

namespace SelectedSameAModuleSplitExplicit318

universe u
variable {R L M N : Type u} [Ring R]
variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

variable (f : L →ₗ[R] M) (g : M →ₗ[R] N) (hex : Function.Exact f g)

include hex in
private theorem fg_zero (a : L) : g (f a) = 0 := (hex (f a)).2 ⟨a, rfl⟩

include hex in
/-- The literal linear maps, not an independently chosen complex. -/
@[expose] def row : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact fg_zero f g hex a)

variable (r : M →ₗ[R] L) (hr : Function.LeftInverse r f)
variable (hSurj : Function.Surjective g)

include hr hex hSurj in
/-- Correct a chosen preimage by its actual retracted first component. The
resulting additive and scalar linear map is independent of the preimages. -/
noncomputable def splitting : (row f g hex).Splitting := by
  let P : M →ₗ[R] M := LinearMap.id - f.comp r
  have hp (z : M) : P z = z - f (r z) := rfl
  have hPf (a : L) : P (f a) = 0 := by rw [hp, hr, sub_self]
  have hgP (z : M) : g (P z) = g z := by
    rw [hp, map_sub, fg_zero f g hex, sub_zero]
  have hP (z w : M) (h : g z = g w) : P z = P w := by
    have hzero : g (z - w) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨a, ha⟩ := (hex (z - w)).1 hzero
    apply sub_eq_zero.mp
    rw [← map_sub, ← ha, hPf]
  let choose (y : N) := Classical.choose (hSurj y)
  have hchoose (y : N) : g (choose y) = y := Classical.choose_spec (hSurj y)
  let s : N →ₗ[R] M :=
    { toFun := fun y => P (choose y)
      map_add' := by
        intro a b
        change P (choose (a + b)) = P (choose a) + P (choose b)
        rw [← map_add]
        apply hP
        rw [hchoose, map_add, hchoose, hchoose]
      map_smul' := by
        intro c a
        change P (choose (c • a)) = c • P (choose a)
        rw [← map_smul]
        apply hP
        rw [hchoose, map_smul, hchoose] }
  refine { r := ModuleCat.ofHom r, s := ModuleCat.ofHom s, f_r := ?_, s_g := ?_, id := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact hr
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change g (P (choose y)) = y
    exact (hgP (choose (show N from y))).trans (hchoose (show N from y))
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change f (r z) + P (choose (g z)) = z
    have hid (w : M) : f (r w) + P (choose (g w)) = w := by
      rw [hP (choose (g w)) w (hchoose (g w)), hp]
      rw [add_comm (f (r w)), sub_add_cancel]
    exact hid (show M from z)

end SelectedSameAModuleSplitExplicit318
