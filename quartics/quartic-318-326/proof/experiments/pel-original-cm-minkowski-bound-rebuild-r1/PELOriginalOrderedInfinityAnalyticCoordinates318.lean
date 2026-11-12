module
public import FourRootInfinityEvaluationNeighborhood318
public import PELOriginalOrderedFiniteAnalyticCoordinates318
public section
noncomputable section
namespace PELOriginalOrderedInfinityAnalyticCoordinates318
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalOrderedCharacterCoordinate318 PELOriginalOrderedCharacterSchemeMaps318
open FourRootInfinityEvaluationNeighborhood318
abbrev N (i:Fin 4):=Neighborhood branches (PELOriginalCharacterInfinityMaps318.indices i)
@[expose] def scale (i:Fin 4):ℂ:=ThreeBranchLegendreInfinityAlgebra318.scale (branch i 0) (branch i 1)
@[expose] def targetEvaluation (i:Fin 4) (p:N i):InfinityChart318.Ring (A i) (B i)→ₐ[ℂ]ℂ:=
  (lift branches (PELOriginalCharacterInfinityMaps318.indices i) p).comp
    (PELOriginalCharacterInfinityMaps318.mapOnRings i)
@[expose] def infinityMap (i:Fin 4) (p:N i):LegendrePlaneOverlap318.InfinityPlane (parameter i):=
  ⟨(targetEvaluation i p (InfinityChart318.x (A i) (B i)),
    targetEvaluation i p (InfinityChart318.z (A i) (B i))),by
    have h:=congrArg (targetEvaluation i p) (InfinityChart318.relation (A i) (B i))
    simpa only [map_sub,map_mul,map_pow,map_zero,AlgHom.commutes,
      Algebra.algebraMap_self,RingHom.id_apply] using h⟩
lemma coordinate_x (i:Fin 4) (p:N i):
    (infinityMap i p).val.1=scale i*p.val.val.1*
      (1+(branches 0-center i)*p.val.val.1^2)*
        (product branches (PELOriginalCharacterInfinityMaps318.indices i) p.val)⁻¹:=by
  change targetEvaluation i p (InfinityChart318.x (A i) (B i))=_
  simp only [targetEvaluation,AlgHom.comp_apply,PELOriginalCharacterInfinityMaps318.mapOnRings,
    ThreeBranchLegendreInfinityAlgebra318.infinityMap,PELOriginalOrderedCharacterSchemeMaps318.parameter_eq,InfinityChart318.lift_x,
    map_mul,map_add,map_one,map_pow,AlgHom.commutes,lift_u,lift_inverse]
  rfl
lemma coordinate_z (i:Fin 4) (p:N i):
    (infinityMap i p).val.2=scale i^3*p.val.val.1^3*
      (product branches (PELOriginalCharacterInfinityMaps318.indices i) p.val)⁻¹:=by
  change targetEvaluation i p (InfinityChart318.z (A i) (B i))=_
  simp only [targetEvaluation,AlgHom.comp_apply,PELOriginalCharacterInfinityMaps318.mapOnRings,
    ThreeBranchLegendreInfinityAlgebra318.infinityMap,PELOriginalOrderedCharacterSchemeMaps318.parameter_eq,InfinityChart318.lift_z,
    map_mul,map_pow,AlgHom.commutes,lift_u,lift_inverse]
  rfl
lemma infinity_evaluation (i:Fin 4) (p:N i):
    LegendreNativeChartEvaluations318.infinityEvaluation (parameter i) (infinityMap i p)=
      targetEvaluation i p:=by
  apply InfinityChart318.hom_ext
  · exact LegendreNativeChartEvaluations318.infinity_x _ _
  · exact LegendreNativeChartEvaluations318.infinity_z _ _

/-- The SAME rational infinity substitution is continuous on its actual
principal open. The denominator does not vanish at any original u=0 point. -/
lemma continuous_infinityMap (i:Fin 4):Continuous (infinityMap i):=by
  have hd:Continuous (fun p:N i=>
      (product branches (PELOriginalCharacterInfinityMaps318.indices i) p.val)⁻¹):=
    ((continuous_product branches _).comp continuous_subtype_val).inv₀ (fun p=>p.property)
  have hx:Continuous (fun p:N i=>(infinityMap i p).val.1):=by
    simp_rw [coordinate_x]
    exact (((continuous_const.mul continuous_subtype_val.subtype_val.fst).mul
      (continuous_const.add (continuous_const.mul
        (continuous_subtype_val.subtype_val.fst.pow 2)))).mul hd)
  have hz:Continuous (fun p:N i=>(infinityMap i p).val.2):=by
    simp_rw [coordinate_z]
    exact (continuous_const.mul (continuous_subtype_val.subtype_val.fst.pow 3)).mul hd
  exact (hx.prodMk hz).subtype_mk _
end PELOriginalOrderedInfinityAnalyticCoordinates318
