module
public import PELOriginalCandidatePointEquivalence318
public import LocalizedComplexCoefficientAnalytic318
public section
noncomputable section
namespace PELOriginalCandidateElementFunctions318
open Set PELOriginalCandidateAffineCharts318 PELOriginalCubicRelationIdeal318
open PELOriginalChartAnalyticEvaluation318 PELOriginalLevelTheta318
open PELOriginalRatioEvaluationExt318 PELOriginalRatioRelationEvaluation318
open PELOriginalCandidateAffineOpenImage318 PELOriginalCandidatePointEquivalence318
open PELOriginalAllLevelHolomorphicMap318 ComplexProjectiveComplexAtlas318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- One fixed polynomial in the original ratios for every element of
the WHOLE original coordinate ring, valid simultaneously at all points. -/
@[expose] def expression (a : CoordinateChart τ hτ j) : Equations :=
  (polynomial_surjective τ hτ j a).choose
lemma expression_spec (a : CoordinateChart τ hτ j) :
    MvPolynomial.aeval (ratioElement τ hτ j) (expression τ hτ j a) = a :=
  (polynomial_surjective τ hτ j a).choose_spec

/-- A total continuous polynomial expression on the original ambient
affine model. Its restriction equals actual candidate ring evaluation. -/
@[expose] def elementValue (a : CoordinateChart τ hτ j) (w : TargetModel 1) : ℂ :=
  MvPolynomial.eval (homogeneousVector j w) (expression τ hτ j a)

lemma toPoint_value (a : CoordinateChart τ hτ j) (w : Locus τ hτ j) :
    toPoint τ hτ j w a = elementValue τ hτ j a w.val := by
  calc
    toPoint τ hτ j w a = toPoint τ hτ j w
        (MvPolynomial.aeval (ratioElement τ hτ j) (expression τ hτ j a)) :=
      congrArg (toPoint τ hτ j w) (expression_spec τ hτ j a).symm
    _ = MvPolynomial.eval (fun i => toPoint τ hτ j w (ratioElement τ hτ j i))
        (expression τ hτ j a) := map_polynomial τ hτ j _ _
    _ = elementValue τ hτ j a w.val := by
      rw [show (fun i => toPoint τ hτ j w (ratioElement τ hτ j i)) =
        homogeneousVector j w.val from funext (toPoint_ratio τ hτ j w)]
      rfl

lemma pointVector_value (a : CoordinateChart τ hτ j) (f : Points τ hτ j) :
    elementValue τ hτ j a (pointVector τ hτ j f) = f a := by
  rw [←toPoint_value τ hτ j a (toLocus τ hτ j f),toPoint_toLocus]

lemma homogeneousVector_continuous : Continuous (homogeneousVector j) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  exact ((embed_analytic (Label 3) j ((coordinates (Label 3) 0 j).symm w)).comp
    ((coordinates (Label 3) 0 j).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt w)).continuousAt

lemma polynomial_continuous (p : Equations) :
    Continuous (fun w : TargetModel 1 => MvPolynomial.eval (homogeneousVector j w) p) := by
  have h : Continuous (fun v : Label 3 → ℂ => MvPolynomial.eval v p) :=
    continuous_iff_continuousAt.mpr (fun v =>
      ((AnalyticOnNhd.eval_mvPolynomial p) v (mem_univ v)).continuousAt)
  exact h.comp (homogeneousVector_continuous j)

lemma elementValue_continuous (a : CoordinateChart τ hτ j) :
    Continuous (elementValue τ hτ j a) :=
  polynomial_continuous j (expression τ hτ j a)

/-- The independently defined entire candidate zero locus is closed
in its genuine ambient complex topology, not a transported topology. -/
theorem candidateLocus_closed : IsClosed (candidateLocus τ hτ j) := by
  have hset : candidateLocus τ hτ j =
      ⋂ p : Equations, ⋂ (_ : p ∈ relations τ hτ),
        {w : TargetModel 1 | MvPolynomial.eval (homogeneousVector j w) p = 0} := by
    ext w
    simp only [candidateLocus,mem_setOf_eq,mem_iInter]
  rw [hset]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro hp
  exact isClosed_eq (polynomial_continuous j p) continuous_const
end PELOriginalCandidateElementFunctions318
