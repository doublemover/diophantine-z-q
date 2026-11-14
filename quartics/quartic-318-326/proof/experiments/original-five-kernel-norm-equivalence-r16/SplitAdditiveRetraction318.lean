module
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Abel

public section
noncomputable section
namespace SplitAdditiveRetraction318

variable {S T : Type*} [AddCommGroup S] [AddCommGroup T]
variable (p : T →+ S) (t : S →+ T)

/-- The part of a source element not detected by the given split transfer. -/
@[expose] def residual : S →+ S := AddMonoidHom.id S - p.comp t

theorem residual_apply (x : S) : residual p t x = x - p (t x) := rfl

variable (h : ∀ y, t (p y) = y)
include h

theorem transfer_residual (x : S) : t (residual p t x) = 0 := by
  rw [residual_apply, map_sub, h, sub_self]

theorem residual_pullback (y : T) : residual p t (p y) = 0 := by
  rw [residual_apply, h, sub_self]

/-- A split transfer gives an actual decomposition, retaining its full kernel. -/
@[expose] def equivalence : S ≃+ (T × t.ker) where
  toFun x := (t x, ⟨residual p t x, transfer_residual p t h x⟩)
  invFun z := p z.1 + z.2.val
  left_inv x := by
    change p (t x) + (x - p (t x)) = x
    abel
  right_inv z := by
    apply Prod.ext
    · change t (p z.1 + z.2.val) = z.1
      rw [map_add, h, z.2.property, add_zero]
    · apply Subtype.ext
      change (p z.1 + z.2.val) - p (t (p z.1 + z.2.val)) = z.2.val
      rw [map_add, h, z.2.property, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact t.map_add x y
    · apply Subtype.ext
      exact (residual p t).map_add x y

theorem equivalence_first (x : S) : (equivalence p t h x).1 = t x := rfl

theorem equivalence_second (x : S) :
    ((equivalence p t h x).2 : S) = x - p (t x) := rfl

theorem equivalence_symm_apply (z : T × t.ker) :
    (equivalence p t h).symm z = p z.1 + z.2.val := rfl

/-- The original image and transfer kernel have no nonzero element in common. -/
theorem pullback_eq_kernel_iff (y : T) (z : t.ker) :
    p y = z.val ↔ y = 0 ∧ z.val = 0 := by
  constructor
  · intro hyz
    have hy : y = 0 := by
      have hz := congrArg t hyz
      rw [h, z.property] at hz
      exact hz
    exact ⟨hy, by rw [← hyz, hy, map_zero]⟩
  · rintro ⟨hy, hz⟩
    rw [hy, hz, map_zero]

end SplitAdditiveRetraction318
