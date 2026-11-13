module
public import PELOriginalOrderedCharacterPointEquivalence318
public import LegendreNativeChartEvaluations318
public section
noncomputable section
namespace PELOriginalOrderedFiniteAnalyticCoordinates318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalOrderedCharacterCoordinate318
open FourRootNormalizedPointCharts318

@[expose] def evaluation (p:FinitePoints branches):FourRootAffineCoordinateRing318.Ring branches→ₐ[ℂ]ℂ:=
  (FourRootAffineCoordinateRing318.pointEquiv branches).symm p
@[expose] def targetEvaluation (i:Fin 4) (p:FinitePoints branches):Target i→ₐ[ℂ]ℂ:=
  (evaluation p).comp (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i)
@[expose] def finiteMap (i:Fin 4) (p:FinitePoints branches):LegendreFiniteComplexAtlas318.Plane (parameter i):=
  (LegendreCompletedPointIdentification318.finiteSolutions (parameter i)).symm
    (AffineEquationFunctor318.ofHom (A i) (B i) (targetEvaluation i p))
lemma coordinate_x (i:Fin 4) (p:FinitePoints branches):
    (finiteMap i p).val.1=(difference i)⁻¹*(p.val.1-center i):=by
  change targetEvaluation i p (ShortAffineJacobian318.x (A i) (B i))=_
  simp only [targetEvaluation,AlgHom.comp_apply,finite_x,map_mul,map_sub,AlgHom.commutes]
  simp [evaluation,FourRootAffineCoordinateRing318.pointEquiv]
lemma coordinate_y (i:Fin 4) (p:FinitePoints branches):
    (finiteMap i p).val.2=(rootScale i)⁻¹*
      (p.val.2 (SourceTwistArithmetic318.complement i 0)*
       p.val.2 (SourceTwistArithmetic318.complement i 1)*
       p.val.2 (SourceTwistArithmetic318.complement i 2)):=by
  change targetEvaluation i p (ShortAffineJacobian318.y (A i) (B i))=_
  simp only [targetEvaluation,AlgHom.comp_apply,finite_y_three,map_mul,AlgHom.commutes]
  simp [evaluation,FourRootAffineCoordinateRing318.pointEquiv]
lemma finite_evaluation (i:Fin 4) (p:FinitePoints branches):
    LegendreNativeChartEvaluations318.finiteEvaluation (parameter i) (finiteMap i p)=targetEvaluation i p:=
  (AffineEquationFunctor318.solutionEquiv (A i) (B i)).symm_apply_apply _

/-- Continuity is in the independent affine subspace topologies on both
sides, using exactly the polynomial coordinates of the actual ring map. -/
lemma continuous_finiteMap (i:Fin 4):Continuous (finiteMap i):=by
  have hx:Continuous (fun p:FinitePoints branches=>(finiteMap i p).val.1):=by
    simp_rw [coordinate_x]
    fun_prop
  have hy:Continuous (fun p:FinitePoints branches=>(finiteMap i p).val.2):=by
    simp_rw [coordinate_y]
    fun_prop
  exact (hx.prodMk hy).subtype_mk _
end PELOriginalOrderedFiniteAnalyticCoordinates318
