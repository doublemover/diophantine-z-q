module
public import PELOriginalOrderedInfinityAnalyticCoordinates318
public section
noncomputable section
namespace PELOriginalOrderedCompletedChartSquares318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalOrderedCharacterCoordinate318 FourRootNormalizedPointCharts318
open LegendreCompletedPointIdentification318

/-- The induced map is defined by the actual whole Scheme morphism, NOT
by gluing newly chosen analytic formulas or transporting a topology. -/
@[expose] def schemeMap (i:Fin 4) (x:Completed branches):
    PELOriginalOrderedCharacterPointMap318.Points i:=
  ⟨(FourRootCompletedSchemePoints318.completedPoint branches x).val≫
    PELOriginalWholeCharacterMorphisms318.morphism i,by
    rw [Category.assoc,PELOriginalWholeCharacterMorphisms318.over_complex]
    exact (FourRootCompletedSchemePoints318.completedPoint branches x).property⟩
@[expose] def completedMap (i:Fin 4):Completed branches→LegendrePlaneOverlap318.CompletedPlane (parameter i):=
  (schemeEquivalence (parameter i)).symm ∘ schemeMap i
lemma scheme_value (i:Fin 4) (x:Completed branches):
    schemeEquivalence (parameter i) (completedMap i x)=schemeMap i x:=
  (schemeEquivalence (parameter i)).apply_symm_apply _

lemma finite_square (i:Fin 4) (p:FinitePoints branches):
    completedMap i (finiteChart branches p)=LegendrePlaneOverlap318.finiteChart (parameter i)
      (PELOriginalOrderedFiniteAnalyticCoordinates318.finiteMap i p):=by
  apply (schemeEquivalence (parameter i)).injective
  apply Subtype.ext
  rw [scheme_value,LegendreNativeChartEvaluations318.finite_scheme,
    PELOriginalOrderedFiniteAnalyticCoordinates318.finite_evaluation]
  change (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (PELOriginalOrderedFiniteAnalyticCoordinates318.evaluation p).toRingHom)≫
        FourRootGluedScheme318.finiteChart branches)≫_=_
  rw [Category.assoc,PELOriginalWholeCharacterMorphisms318.on_finite]
  unfold PELOriginalWholeCharacterMorphisms318.finiteMap
    PELOriginalOrderedCharacterSchemeMaps318.morphism
    PELOriginalOrderedFiniteAnalyticCoordinates318.targetEvaluation
  rw [←Category.assoc,←Spec.map_comp] <;> rfl

lemma infinity_lift (i:Fin 4) (p:PELOriginalOrderedInfinityAnalyticCoordinates318.N i):
    Spec.map (CommRingCat.ofHom
      (FourRootInfinityEvaluationNeighborhood318.lift branches
        (PELOriginalCharacterInfinityMaps318.indices i) p).toRingHom)≫
      PELOriginalCharacterRefinedCover318.infinityChart i=
        (FourRootCompletedSchemePoints318.infinityPoint branches p.val).val:=by
  unfold PELOriginalCharacterRefinedCover318.infinityChart
  rw [←Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom _)≫Spec.map (CommRingCat.ofHom _)=
    Spec.map (CommRingCat.ofHom _)
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact FourRootInfinityEvaluationNeighborhood318.lift_on_ring branches _ p

lemma infinity_square (i:Fin 4) (p:PELOriginalOrderedInfinityAnalyticCoordinates318.N i):
    completedMap i (infinityChart branches p.val)=LegendrePlaneOverlap318.infinityChart (parameter i)
      (PELOriginalOrderedInfinityAnalyticCoordinates318.infinityMap i p):=by
  apply (schemeEquivalence (parameter i)).injective
  apply Subtype.ext
  rw [scheme_value,LegendreNativeChartEvaluations318.infinity_scheme,
    PELOriginalOrderedInfinityAnalyticCoordinates318.infinity_evaluation]
  change (FourRootCompletedSchemePoints318.completedPoint branches
    (infinityChart branches p.val)).val≫_=_
  rw [FourRootCompletedSchemePoints318.completed_infinity,←infinity_lift i p,
    Category.assoc,PELOriginalWholeCharacterMorphisms318.on_infinity]
  unfold PELOriginalWholeCharacterMorphisms318.infinityMap
    PELOriginalCharacterInfinityMaps318.morphism
    PELOriginalOrderedInfinityAnalyticCoordinates318.targetEvaluation
  rw [←Category.assoc,←Spec.map_comp] <;> rfl
end PELOriginalOrderedCompletedChartSquares318
