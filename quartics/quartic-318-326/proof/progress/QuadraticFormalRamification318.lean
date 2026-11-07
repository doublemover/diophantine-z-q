module
public import QuadraticFormalDifferent318
public section
noncomputable section
namespace QuadraticFormalRamification318
set_option maxHeartbeats 300000
open PowerSeries QuadraticFormalBasis318 QuadraticFormalDifferent318 IsDiscreteValuationRing
open Submodule.IsPrincipal
variable (k:Type*) [Field k]

theorem root_irreducible : Irreducible (root k) := by
  apply (MulEquiv.irreducible_iff (f:=(toSeries k).toMulEquiv)).mp
  change Irreducible ((toSeries k) ((toSeries k).symm X))
  rw [RingEquiv.apply_symm_apply]
  exact PowerSeries.X_irreducible

theorem two_unit (h2:(2:k)≠0) : IsUnit (2:Cover k) := by
  have h: IsUnit (C (2:k):k⟦X⟧) := (isUnit_iff_ne_zero.mpr h2).map C
  have hh:=h.map (toSeries k).symm.toRingHom
  simpa only [map_ofNat] using hh

theorem different_eq_maximal (h2:(2:k)≠0) :
    differentIdeal k⟦X⟧ (Cover k)=IsLocalRing.maximalIdeal (Cover k) := by
  rw [different_eq k h2,Ideal.span_singleton_mul_left_unit (two_unit k h2)]
  exact (root_irreducible k).maximalIdeal_eq.symm

/-- The actual covering uniformizer has canonical DVR value one. -/
theorem root_value : addVal (Cover k) (root k)=1 :=
  addVal_def _ 1 (root_irreducible k) 1 (by simp)

/-- The actual base uniformizer has ramification index two. -/
theorem base_value : addVal (Cover k) (algebraMap k⟦X⟧ (Cover k) X)=2 := by
  rw [base_parameter,addVal_pow,root_value]
  norm_num

/-- The canonical exponent of the actual different ideal is exactly one. -/
theorem different_exponent_one (h2:(2:k)≠0) :
    (addVal (Cover k) (generator (differentIdeal k⟦X⟧ (Cover k)))).toNat=1 := by
  have ha:Associated (generator (differentIdeal k⟦X⟧ (Cover k))) (2*root k) := by
    rw [different_eq k h2]
    exact associated_generator_span_self _
  have hv:= (addVal_eq_iff_associated _ _).mpr ha
  rw [hv,addVal_mul,addVal_eq_zero_iff.mpr (two_unit k h2),root_value]
  simp

end QuadraticFormalRamification318
