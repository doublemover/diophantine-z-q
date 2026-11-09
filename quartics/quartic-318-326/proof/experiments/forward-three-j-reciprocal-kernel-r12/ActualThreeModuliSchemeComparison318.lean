module
public import ThreeJModuliEvaluation318
public import ActualThreeProjectivePoints318
public section
noncomputable section
namespace ActualThreeModuliSchemeComparison318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJModuliOpen318 ThreeJModuliScheme318 ThreeJModuliEvaluation318
open ThreeCompactParameter318 LiteralThreeCompactParameter318
open ThreeArithmeticQuotient318 ActualThreeProjectivePoints318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def parameterPoint (z : ParameterOpen) : Spec (CommRingCat.of ℂ) ⟶
    ThreeJModuliScheme318.Source := Spec.map (CommRingCat.ofHom (evaluation z).toRingHom)

/-- Evaluation in the constructed rational open is the original finite
polynomial-evaluation chart point of the projective source scheme. -/
theorem parameterPoint_embedding (z : ParameterOpen) :
    parameterPoint z ≫ embedding=(ProjectiveLineFieldPoints318.chartPoint (R:=ℚ) 1 z.val).val := by
  unfold parameterPoint embedding toLaurent ProjectiveLineOverlap318.embedding
    ProjectiveLineOverlap318.finiteInclusion
  simp only [←Category.assoc,←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    change evaluation z (inclusion (algebraMap ℚ[X] ThreeJLaurentEquiv318.Laurent
      (Polynomial.C q)))=Polynomial.aeval (R:=ℚ) z.val (Polynomial.C q)
    rw [evaluation_inclusion]
    simp only [laurentEvaluation,IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq]
  · change evaluation z (inclusion ProjectiveLineOverlap318.t)=
      Polynomial.aeval (R:=ℚ) z.val Polynomial.X
    rw [evaluation_inclusion,laurent_t,Polynomial.aeval_X]

/-- Exact comparison on actual scheme morphisms, not just agreement after
forgetting to j. The target is the original arithmetic fixed algebra. -/
theorem parameterPoint_arithmetic (z : ParameterOpen) :
    parameterPoint z ≫ arithmeticMap=
      ThreeArithmeticQuotient318.schemePoint 3 ((sourceParameter 3).symm z) := by
  rw [parameterPoint,arithmeticMap,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((evaluation z).toRingHom.comp
    ThreeJArithmeticAlgebraMap318.fixedMap))=_
  rw [arithmetic_evaluation]
  rfl

@[expose] def sourcePoint (q : ThreeArithmeticQuotient318.Source) :
    Spec (CommRingCat.of ℂ) ⟶ ThreeJModuliScheme318.Source :=
  parameterPoint (sourceParameter 3 q)

/-- Restricting the independently constructed compact analytic/algebraic
comparison gives exactly the constructed rational open source point. -/
theorem sourcePoint_compact (q : ThreeArithmeticQuotient318.Source) :
    sourcePoint q ≫ embedding=
      (compactPointHomeomorph (ActualThreeCuspFilling318.original q.val)).val := by
  rw [sourcePoint,parameterPoint_embedding,compactPointHomeomorph_original,
    ActualThreeExceptionalParameter318.quotientParameter_restrict 3 q]

/-- The compact comparison and rational arithmetic scheme map commute
with the existing actual Γ1(3) comparison on every point of its full old domain. -/
theorem sourcePoint_arithmetic (q : ThreeArithmeticQuotient318.Source) :
    sourcePoint q ≫ arithmeticMap=ThreeArithmeticQuotient318.schemePoint 3 q := by
  rw [sourcePoint,parameterPoint_arithmetic,Homeomorph.symm_apply_apply]

/-- The exact original period point1/3, not a relabeled division root, is
retained by this arithmetic scheme comparison. -/
theorem sourcePoint_period (tau : UpperHalfPlane)
    (h : OpenJComplexEvaluation318.Admissible tau) :
    sourcePoint (ThreeArithmeticQuotient318.projection tau h) ≫ arithmeticMap=
      Spec.map (CommRingCat.ofHom (ThreeArithmeticPoint318.fixedPoint 3 tau h)) := by
  rw [sourcePoint_arithmetic,ThreeArithmeticQuotient318.schemePoint_projection]

/-- The same point on the constructed compact projective source has its
original genuine j value under the exact global finite scheme morphism. -/
theorem sourcePoint_global_j (q : ThreeArithmeticQuotient318.Source) :
    sourcePoint q ≫ embedding ≫ ThreeProjectiveJMap318.map=
      (ProjectiveLineFieldPoints318.chartPoint (R:=ℚ) 1
        (QuotientJ318.jMap 3 q.val)).val := by
  rw [←Category.assoc,sourcePoint_compact]
  change (ThreeProjectiveJPoints318.mapPoints
    (compactPointHomeomorph (ActualThreeCuspFilling318.original q.val))).val=_
  exact congrArg Subtype.val (ActualThreeCompactJPoints318.original_value q.val)

end ActualThreeModuliSchemeComparison318
