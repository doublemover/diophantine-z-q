module
public import Mathlib.Algebra.Module.Equiv.Basic
public section
noncomputable section
namespace UnitModuleScalar318
universe u
variable {R:Type u} [CommRing R]
lemma apply_eq (e:R≃ₗ[R]R) (x:R):e x=x*e 1:=by
  simpa only [smul_eq_mul,mul_one] using e.map_smul x 1
/-- The actual scalar of an invertible rank-one linear map, including its
explicit inverse rather than a nonzero-value assertion. -/
@[expose] def unit (e:R≃ₗ[R]R):Rˣ where
  val:=e 1
  inv:=e.symm 1
  val_inv:=by
    have h:=e.apply_symm_apply 1
    rw [apply_eq] at h
    exact (mul_comm _ _).trans h
  inv_val:=by
    have h:=e.apply_symm_apply 1
    rw [apply_eq] at h
    exact h
@[simp] lemma unit_val (e:R≃ₗ[R]R):(unit e).val=e 1:=rfl
lemma value_apply (e:R≃ₗ[R]R) (x:R):e x=(unit e).val*x:=
  (apply_eq e x).trans (mul_comm _ _)
lemma unique (e:R≃ₗ[R]R) (a:Rˣ) (h:∀x,e x=a.val*x):unit e=a:=by
  apply Units.ext
  simpa using h 1
@[simp] lemma refl:unit (LinearEquiv.refl R R)=1:=by apply Units.ext;rfl
lemma trans (e f:R≃ₗ[R]R):unit (e.trans f)=unit e*unit f:=by
  apply Units.ext
  exact apply_eq f (e 1)
@[simp] lemma symm (e:R≃ₗ[R]R):unit e.symm=(unit e)⁻¹:=by apply Units.ext;rfl
end UnitModuleScalar318
