module
public import PELOriginalCandidateAffineOpenImage318
public import PELOriginalRatioRelationEvaluation318
public section
noncomputable section
namespace PELOriginalCandidatePointEquivalence318
open PELOriginalCandidateAffineCharts318 PELOriginalCubicRelationIdeal318
open PELOriginalChartAnalyticEvaluation318 PELOriginalLevelTheta318
open PELOriginalRatioEvaluationExt318 PELOriginalRatioRelationEvaluation318
open PELOriginalCandidateAffineOpenImage318 PELOriginalAllLevelHolomorphicMap318
open ComplexProjectiveComplexAtlas318 ComplexProjectiveRatioCharts318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

abbrev Points := CoordinateChart τ hτ j →ₐ[ℂ] ℂ
abbrev Locus := {w : TargetModel 1 // w ∈ candidateLocus τ hτ j}

@[expose] def pointVector (f : Points τ hτ j) : TargetModel 1 :=
  coordinates (Label 3) 0 j (fun i => f (ratioElement τ hτ j i.val))

lemma homogeneousVector_pointVector (f : Points τ hτ j) :
    homogeneousVector j (pointVector τ hτ j f) = fun i => f (ratioElement τ hτ j i) := by
  funext i
  by_cases hi : i = j
  · subst i
    rw [homogeneousVector_at,ratio_self,map_one]
  · simp only [homogeneousVector,pointVector,LinearEquiv.symm_apply_apply,embed,dif_neg hi]

lemma pointVector_mem (f : Points τ hτ j) : pointVector τ hτ j f ∈ candidateLocus τ hτ j := by
  change ∀ p ∈ relations τ hτ, MvPolynomial.eval (homogeneousVector j (pointVector τ hτ j f)) p = 0
  rw [homogeneousVector_pointVector]
  exact point_relations τ hτ j f

@[expose] def toLocus (f : Points τ hτ j) : Locus τ hτ j :=
  ⟨pointVector τ hτ j f,pointVector_mem τ hτ j f⟩

@[expose] def toPoint (w : Locus τ hτ j) : Points τ hτ j :=
  PELOriginalCandidateVectorEvaluation318.evaluation τ hτ j (homogeneousVector j w.val) w.property
    (by rw [homogeneousVector_at]; exact one_ne_zero)

lemma toPoint_ratio (w : Locus τ hτ j) (i : Label 3) :
    toPoint τ hτ j w (ratioElement τ hτ j i) = homogeneousVector j w.val i := by
  rw [toPoint,PELOriginalCandidateVectorEvaluation318.evaluation_ratio,homogeneousVector_at,div_one]

lemma toPoint_toLocus (f : Points τ hτ j) : toPoint τ hτ j (toLocus τ hτ j f) = f := by
  have h : (toPoint τ hτ j (toLocus τ hτ j f)).toRingHom = f.toRingHom := by
    apply ringHom_ext_ratios τ hτ j
    · intro c
      rw [(toPoint τ hτ j (toLocus τ hτ j f)).commutes,f.commutes]
    · intro i
      change toPoint τ hτ j (toLocus τ hτ j f) (ratioElement τ hτ j i) = _
      rw [toPoint_ratio]
      exact congrFun (homogeneousVector_pointVector τ hτ j f) i
  ext a
  exact congrArg (fun h : CoordinateChart τ hτ j →+* ℂ => h a) h

lemma toLocus_toPoint (w : Locus τ hτ j) : toLocus τ hτ j (toPoint τ hτ j w) = w := by
  apply Subtype.ext
  change coordinates (Label 3) 0 j (fun i => toPoint τ hτ j w (ratioElement τ hτ j i.val)) = w.val
  have hr : (fun i : {i : Label 3 // i ≠ j} => toPoint τ hτ j w (ratioElement τ hτ j i.val)) =
      (fun i : {i : Label 3 // i ≠ j} => homogeneousVector j w.val i.val / homogeneousVector j w.val j) := by
    funext i
    rw [toPoint_ratio,homogeneousVector_at,div_one]
  rw [hr,normalized_ratios]

lemma toPoint_coordinate (w : Locus τ hτ j)
    (i : PELOriginalProjectedChartIndependence318.TargetIndex) :
    toPoint τ hτ j w (PELOriginalProjectedChartIndependence318.coordinateElement τ hτ j i) = w.val i := by
  have h := congrArg Subtype.val (toLocus_toPoint τ hτ j w)
  exact congrFun h i

/-- Both inverse maps between ALL ordinary complex points of the whole
original chart and the independently defined full ambient candidate
zero locus. Neither side is restricted to an analytic image or open. -/
@[expose] def equivalence : Points τ hτ j ≃ Locus τ hτ j where
  toFun := toLocus τ hτ j
  invFun := toPoint τ hτ j
  left_inv := toPoint_toLocus τ hτ j
  right_inv := toLocus_toPoint τ hτ j
end PELOriginalCandidatePointEquivalence318
