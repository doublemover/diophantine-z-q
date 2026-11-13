module
public import LegendreCompletedPointIdentification318
public import WeierstrassActualChartComparison318
public section
noncomputable section
namespace LegendreNativeChartEvaluations318
open AlgebraicGeometry CategoryTheory
open LegendrePlaneOverlap318 LegendreFiniteComplexAtlas318
open LegendreCompletedPointIdentification318 NormalizedLegendreProjectiveModel318
variable (l:ℂ) [Fact (l≠0 ∧ l≠1)]

@[expose] def finiteEvaluation (p:Plane l):ShortAffineJacobian318.Ring (A l) (B l)→ₐ[ℂ]ℂ:=
  AffineEquationFunctor318.toHom (A l) (B l) (finiteSolutions l p)
lemma finite_x (p:Plane l):finiteEvaluation l p (ShortAffineJacobian318.x (A l) (B l))=p.val.1:=
  AffineEquationFunctor318.toHom_x _ _ _
lemma finite_y (p:Plane l):finiteEvaluation l p (ShortAffineJacobian318.y (A l) (B l))=p.val.2:=
  AffineEquationFunctor318.toHom_y _ _ _
lemma finite_scheme (p:Plane l):
    (schemeEquivalence l (finiteChart l p)).val=
      Spec.map (CommRingCat.ofHom (finiteEvaluation l p).toRingHom)≫
        WeierstrassGluing318.finiteChart (A l) (B l):=by
  rw [scheme_finite]
  rfl

@[expose] def infinityEvaluation (p:InfinityPlane l):InfinityChart318.Ring (A l) (B l)→ₐ[ℂ]ℂ:=
  InfinityChart318.lift _ _ p.val.1 p.val.2 (by
    simpa only [Algebra.algebraMap_self,RingHom.id_apply] using p.property)
lemma infinity_x (p:InfinityPlane l):infinityEvaluation l p (InfinityChart318.x (A l) (B l))=p.val.1:=
  InfinityChart318.lift_x _ _ _ _ _
lemma infinity_z (p:InfinityPlane l):infinityEvaluation l p (InfinityChart318.z (A l) (B l))=p.val.2:=
  InfinityChart318.lift_z _ _ _ _ _
lemma origin_evaluation:infinityEvaluation l (origin l)=InfinityChart318.origin (A l) (B l):=by
  apply InfinityChart318.hom_ext <;>
    simp only [infinity_x,infinity_z,origin,InfinityChart318.origin_x,InfinityChart318.origin_z]

/-- Evaluation in the entire actual infinity chart agrees with the old
completed Scheme-point equivalence, not just at its distinguished origin. -/
lemma infinity_scheme (p:InfinityPlane l):
    (schemeEquivalence l (infinityChart l p)).val=
      Spec.map (CommRingCat.ofHom (infinityEvaluation l p).toRingHom)≫
        WeierstrassGluing318.infinityChart (A l) (B l):=by
  by_cases hz:p.val.2=0
  · rw [infinity_zero l p hz,scheme_origin,origin_evaluation]
    change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))≫
      (Spec.map (CommRingCat.ofHom (InfinityChart318.origin (A l) (B l)).toRingHom)≫
        WeierstrassGluing318.infinityChart (A l) (B l))=_
    simp only [Algebra.algebraMap_self,CommRingCat.ofHom_id,Spec.map_id,Category.id_comp]
  · rw [scheme_infinity l p hz]
    change Spec.map (CommRingCat.ofHom (finiteEvaluation l (toFinite l p)).toRingHom)≫
      WeierstrassGluing318.finiteChart (A l) (B l)=_
    apply WeierstrassActualChartComparison318.scheme_square
    · rw [infinity_x,finite_x,infinity_z,toFinite_value l p hz]
      exact (div_mul_cancel₀ _ hz).symm
    · rw [finite_y,infinity_z,toFinite_value l p hz]
      exact div_mul_cancel₀ _ hz
end LegendreNativeChartEvaluations318
