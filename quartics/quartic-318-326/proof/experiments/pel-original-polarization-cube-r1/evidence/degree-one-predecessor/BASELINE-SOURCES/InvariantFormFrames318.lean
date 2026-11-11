module
public import InvariantChartForms318
public import WeierstrassKaehler318
public section
noncomputable section
namespace InvariantFormFrames318
open KaehlerDifferential DifferentialChartMaps318 InvariantChartForms318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

theorem finite_frame_value (A B : R) :
    WeierstrassKaehler318.affineFrame A B 1 (finite A B)=
      IsLocalization.Away.invSelf (S := FiniteChart A B) (ShortAffineJacobian318.presentation A B 1).jacobian := by
  rw [InvariantChartForms318.finite,map_smul,WeierstrassKaehler318.affineFrame_dx,smul_eq_mul,mul_one]

theorem infinity_frame_value (A B : R) :
    WeierstrassKaehler318.infinityFrame A B (infinity A B)=
      -IsLocalization.Away.invSelf (S := InfinityChart A B) (InfinityChart318.presentation A B).jacobian := by
  rw [infinity,map_smul,WeierstrassKaehler318.infinityFrame_dx,smul_eq_mul,mul_one]

/-- Each actual invariant form is a generator of the whole relative differential module. -/
theorem finite_generates (A B : R) :
    Submodule.span (FiniteChart A B) (Set.singleton (finite A B))=⊤ := by
  apply top_le_iff.mp
  intro ω _
  apply Submodule.mem_span_singleton.mpr
  refine ⟨WeierstrassKaehler318.affineFrame A B 1 ω *
    algebraMap (WeierstrassOverlap318.Affine A B) (FiniteChart A B)
      (ShortAffineJacobian318.presentation A B 1).jacobian,?_⟩
  apply (WeierstrassKaehler318.affineFrame A B 1).injective
  rw [map_smul,finite_frame_value,smul_eq_mul,mul_assoc,
    IsLocalization.Away.mul_invSelf,mul_one]

theorem infinity_generates (A B : R) :
    Submodule.span (InfinityChart A B) (Set.singleton (infinity A B))=⊤ := by
  apply top_le_iff.mp
  intro ω _
  apply Submodule.mem_span_singleton.mpr
  refine ⟨-WeierstrassKaehler318.infinityFrame A B ω *
    algebraMap (WeierstrassOverlap318.Infinity A B) (InfinityChart A B)
      (InfinityChart318.presentation A B).jacobian,?_⟩
  apply (WeierstrassKaehler318.infinityFrame A B).injective
  rw [map_smul,infinity_frame_value,smul_eq_mul,neg_mul, neg_mul_neg,mul_assoc,
    IsLocalization.Away.mul_invSelf,mul_one]
end InvariantFormFrames318
