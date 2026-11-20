module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.Ring
public section
noncomputable section
open scoped TensorProduct

namespace SelectedIntegralSectionLine318

variable {O L H : Type*} [CommRing O] [CommRing L] [Algebra O L]
variable [AddCommGroup H] [Module O H]

/-- Genuine scalar extension of the actual integral linear functional
on the section line, followed by the canonical L ⊗_O O ≃ L. -/
@[expose] def scalarEval (φ : H →ₗ[O] O) : L ⊗[O] H →ₗ[L] L :=
  (TensorProduct.AlgebraTensorModule.rid O L L).toLinearMap.comp (φ.baseChange L)

theorem scalarEval_tmul (φ : H →ₗ[O] O) (r : L) (x : H) :
    scalarEval φ (r ⊗ₜ[O] x) = algebraMap O L (φ x) * r := by
  simp only [scalarEval,LinearMap.comp_apply,LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe,TensorProduct.AlgebraTensorModule.rid_tmul,Algebra.smul_def]

/-- With the fixed integral frame, the actual generic value on the
relative differential is its frame coefficient times the integral
evaluation of the functional on the frame generator. -/
theorem generic_value_in_frame (φ : H →ₗ[O] O) (e : H ≃ₗ[O] O)
    (ω : L ⊗[O] H) :
    scalarEval φ ω =
      scalarEval e.toLinearMap ω * algebraMap O L (φ (e.symm 1)) := by
  have hφ (x : H) : φ x = e x * φ (e.symm 1) := by
    have hx : x = e x • e.symm 1 := by
      apply e.injective
      rw [map_smul,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]
    calc
      φ x = φ (e x • e.symm 1) := congrArg φ hx
      _ = _ := by rw [map_smul,smul_eq_mul]
  induction ω using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [scalarEval_tmul,scalarEval_tmul,hφ,map_mul]
    ring
  | add ω η hω hη =>
    simp only [map_add,hω,hη,add_mul]

/-- The actual evaluation of a regular affine dual at the actual
generic dJ supplies the same integral numerator in this very frame. -/
theorem integral_ratio (φ : H →ₗ[O] O) (e : H ≃ₗ[O] O)
    (ω : L ⊗[O] H) (a : L) (evaluation : scalarEval φ ω = a) :
    ∃ t : O, scalarEval e.toLinearMap ω * algebraMap O L t = a :=
  ⟨φ (e.symm 1), (generic_value_in_frame φ e ω).symm.trans evaluation⟩


variable {H' : Type*} [AddCommGroup H'] [Module O H']

theorem scalarEval_comp (φ : H' →ₗ[O] O) (α : H →ₗ[O] H') (ω : L ⊗[O] H) :
    scalarEval φ (α.baseChange L ω) = scalarEval (φ.comp α) ω := by
  simp only [scalarEval,LinearMap.comp_apply,LinearMap.baseChange_comp]

/-- Produce the integral comparison factor by evaluating the ACTUAL
comparison map on the generator, and track the same generic vector
under scalar extension. No scalar comparison is a separate hypothesis. -/
theorem scalarEval_canonical_frame
    (eOld : H ≃ₗ[O] O) (eNew : H' ≃ₗ[O] O)
    (α : H →ₗ[O] H') (ω : L ⊗[O] H) :
    scalarEval eNew.toLinearMap (α.baseChange L ω) =
      algebraMap O L (eNew (α (eOld.symm 1))) * scalarEval eOld.toLinearMap ω := by
  rw [scalarEval_comp,generic_value_in_frame (e := eOld)]
  change _ * algebraMap O L (eNew (α (eOld.symm 1))) = _
  exact mul_comm _ _

end SelectedIntegralSectionLine318

#print axioms SelectedIntegralSectionLine318.generic_value_in_frame
#print axioms SelectedIntegralSectionLine318.integral_ratio
#print axioms SelectedIntegralSectionLine318.scalarEval_canonical_frame
