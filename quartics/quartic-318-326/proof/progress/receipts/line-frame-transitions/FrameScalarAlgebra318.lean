module
public import UnitModuleScalar318
public section
noncomputable section
namespace FrameScalarAlgebra318
universe u v
variable {R:Type u} [CommRing R] {P:Type v} [AddCommGroup P] [Module R P]
/-- The unique coordinate-change unit, with left coordinates equal to this
unit times right coordinates. -/
@[expose] def scalar (e f:R≃ₗ[R]P):Rˣ:=UnitModuleScalar318.unit (f.trans e.symm)
lemma relation (e f:R≃ₗ[R]P) (x:R):e ((scalar e f).val*x)=f x:=by
  change e ((UnitModuleScalar318.unit (f.trans e.symm)).val*x)=f x
  rw [←UnitModuleScalar318.value_apply (f.trans e.symm) x]
  exact e.apply_symm_apply (f x)
lemma unique (e f:R≃ₗ[R]P) (a:Rˣ) (h:∀x,e (a.val*x)=f x):scalar e f=a:=by
  apply UnitModuleScalar318.unique
  intro x
  exact (congrArg e.symm (h x)).symm.trans (e.symm_apply_apply _)
@[simp] lemma self (e:R≃ₗ[R]P):scalar e e=1:=by
  apply unique
  intro x
  simp
lemma comp (e f g:R≃ₗ[R]P):scalar e f*scalar f g=scalar e g:=by
  symm
  apply unique
  intro x
  change e (((scalar e f).val*(scalar f g).val)*x)=g x
  rw [mul_assoc,relation,relation]
lemma symm (e f:R≃ₗ[R]P):scalar f e=(scalar e f)⁻¹:=by
  apply eq_inv_of_mul_eq_one_left
  rw [comp,self]
/-- Exact frame-change coboundary identity on the original coefficient ring. -/
lemma gauge (e f d c:R≃ₗ[R]P):
    scalar d c=(scalar d e*(scalar c f)⁻¹)*scalar e f:=by
  rw [←symm c f]
  calc
    scalar d c=scalar d e*(scalar e f*scalar f c):=by rw [comp,comp]
    _=(scalar d e*scalar f c)*scalar e f:=by ac_rfl
end FrameScalarAlgebra318
