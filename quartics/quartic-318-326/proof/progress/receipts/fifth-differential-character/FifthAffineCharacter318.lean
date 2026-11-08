module
public import FifthOpenSigns318
public section
noncomputable section
namespace FifthAffineCharacter318
open SourceTwistArithmetic318 FifthOverlapCoordinates318 FifthInvariantScalar318 FifthOpenSigns318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
lemma smul_swap {K V:Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (a b:K) (v:V):a • (b • v)=b • (a • v):=by
  rw [smul_smul,smul_smul,mul_comm]
/-- Exact full-root eigenrelation in the actual common-open differential module. -/
theorem glued_form (b:Fin 4→Bool):
    AlgHomDifferential318.map (sign b) FifthGlobalIndependence318.form=
      algebraMap ℚ O (epsilon b) • FifthGlobalIndependence318.form:=by
  apply (ContactUnbranchedDifferentialFrame318.frame units).injective
  apply SourceOpenFractionField318.openEmbedding_injective units
  rw [raw_pullback,map_smul,smul_eq_mul,map_mul,RingHom.map_rat_algebraMap,
    FifthGlobalIndependence318.raw_formula,sign_full_inverse]
/-- The same exact character on the actual fifth invariant pullback, preserving
its checked -41160 normalization rather than silently rescaling it. -/
theorem actual_form (b:Fin 4→Bool):
    AlgHomDifferential318.map (sign b) FifthOverlapDifferentialEquation318.pulled=
      algebraMap ℚ O (epsilon b) • FifthOverlapDifferentialEquation318.pulled:=by
  calc
    _=AlgHomDifferential318.map (sign b)
      (algebraMap ℚ O scale • FifthGlobalIndependence318.form):=congrArg (AlgHomDifferential318.map (sign b)) form_eq
    _=algebraMap ℚ O scale • (algebraMap ℚ O (epsilon b) • FifthGlobalIndependence318.form):=by
      rw [AlgHomDifferential318.map_smul,AlgHom.commutes,glued_form]
    _=algebraMap ℚ O (epsilon b) • FifthOverlapDifferentialEquation318.pulled:=by
      rw [form_eq]
      exact smul_swap (K:=O) (V:=KaehlerDifferential ℚ O) _ _ _
end FifthAffineCharacter318
