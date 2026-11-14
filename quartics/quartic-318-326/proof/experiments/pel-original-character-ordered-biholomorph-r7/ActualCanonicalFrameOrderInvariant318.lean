module
public import ActualDvrMeromorphicOrder318
public import EtaleDifferentialFrame318
public section
noncomputable section
namespace ActualCanonicalFrameOrderInvariant318
open TensorProduct
open scoped TensorProduct
variable {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]
@[expose] def transition(e f:M≃ₗ[R]R):R:=f (e.symm 1)
lemma coefficient_change(e f:M≃ₗ[R]R)(ω:M):f ω=transition e f*e ω:=by
  have h:ω=e ω • e.symm 1:=by
    apply e.injective
    rw [map_smul,e.apply_symm_apply,smul_eq_mul,mul_one]
  calc
    f ω=f (e ω • e.symm 1):=congrArg f h
    _=e ω*transition e f:=by rw [map_smul,smul_eq_mul];rfl
    _=transition e f*e ω:=mul_comm _ _
lemma transition_unit(e f:M≃ₗ[R]R):IsUnit (transition e f):=by
  have h:transition e f*transition f e=1:=by
    have he:=coefficient_change e f (f.symm 1)
    rw [f.apply_symm_apply] at he
    exact he.symm
  exact isUnit_iff_exists_inv.mpr ⟨transition f e,h⟩
variable (K:Type*) [Field K] [Algebra R K]
@[expose] def genericFrame(e:M≃ₗ[R]R):(K⊗[R]M)≃ₗ[K]K:=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid R K K
lemma generic_tmul(e:M≃ₗ[R]R)(a:K)(ω:M):genericFrame K e (a⊗ₜ[R]ω)=a*algebraMap R K (e ω):=by
  simp only [genericFrame,LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul,Algebra.smul_def]
  ring
lemma generic_coefficient_change(e f:M≃ₗ[R]R)(ω:K⊗[R]M):
    genericFrame K f ω=algebraMap R K (transition e f)*genericFrame K e ω:=by
  induction ω using TensorProduct.inductionOn with
  | tmul a ω=>
    rw [generic_tmul,generic_tmul,coefficient_change e f ω,map_mul]
    ring
  | add ω η hω hη=>rw [map_add,map_add,hω,hη,mul_add]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
/-- Normalized meromorphic coefficient order is independent of ANY
genuine intrinsic local rank-one frame: the transition is derived to
be a local unit, and the actual extended DVR valuation kills it. -/
theorem value_independent(e f:M≃ₗ[R]R)(ω:K⊗[R]M):
    ActualDvrMeromorphicOrder318.value R K (genericFrame K f ω)=
      ActualDvrMeromorphicOrder318.value R K (genericFrame K e ω):=by
  rw [generic_coefficient_change,(ActualDvrMeromorphicOrder318.value R K).map_mul,
    ActualDvrMeromorphicOrder318.value_unit R K _ (transition_unit e f),zero_add]
theorem order_independent(e f:M≃ₗ[R]R)(ω:K⊗[R]M):
    ActualDvrMeromorphicOrder318.order R K (genericFrame K f ω)=
      ActualDvrMeromorphicOrder318.order R K (genericFrame K e ω):=by
  unfold ActualDvrMeromorphicOrder318.order
  rw [value_independent]
end ActualCanonicalFrameOrderInvariant318
