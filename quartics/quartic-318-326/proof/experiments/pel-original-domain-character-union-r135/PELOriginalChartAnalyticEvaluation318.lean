module
public import PELOriginalCandidateChartFiniteType318
public import HomogeneousQuotientPointEvaluation318
public import PELOriginalAllLevelHolomorphicMap318
public section
noncomputable section
namespace PELOriginalChartAnalyticEvaluation318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalCubicRelationIdeal318 PELOriginalHomogeneousRelationVanishing318
open PELOriginalCandidateAffineCharts318 PELOriginalChartSectionField318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelProjectiveMap318 PELOriginalPolarizationTransitions318
open HomogeneousQuotientChart318
variable (τ:ℂ)(hτ:0<τ.im)

lemma relation_evaluation(q:Base τ)(p:Equations)(hp:p∈relations τ hτ):
    MvPolynomial.eval (baseVector τ hτ 1 q) p=0:=by
  rw [←MvPolynomial.sum_homogeneousComponent p,map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  exact (homogeneous_relation_iff τ hτ _ n (MvPolynomial.homogeneousComponent_mem n p)).mp
    (homogeneous_component_mem τ hτ p hp n) q

lemma actual_cover_scalar(z:ComplexVectors):
    ∃c:ℂ,c≠0∧c • coverVector τ hτ 1 z=baseVector τ hτ 1 (projection (P τ) z):=by
  obtain ⟨c,hc⟩:=(Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    (original_covering_square τ hτ 1 z)
  refine ⟨c,?_,hc⟩
  intro hz
  apply baseVector_nonzero τ hτ 1 (projection (P τ) z)
  rw [←hc,hz,zero_smul]
lemma actual_base_coordinate_nonzero(z:ComplexVectors)(j:Label 3)
    (hj:value τ hτ 3 j z≠0):baseVector τ hτ 1 (projection (P τ) z) j≠0:=by
  obtain ⟨c,hc,he⟩:=actual_cover_scalar τ hτ z
  have h:=congrFun he j
  change c*value τ hτ 3 j z=baseVector τ hτ 1 (projection (P τ) z) j at h
  rw [←h]
  exact mul_ne_zero hc hj
lemma actual_base_ratio(z:ComplexVectors)(j i:Label 3)(hj:value τ hτ 3 j z≠0):
    baseVector τ hτ 1 (projection (P τ) z) i/
        baseVector τ hτ 1 (projection (P τ) z) j=
      value τ hτ 3 i z/value τ hτ 3 j z:=by
  obtain ⟨c,hc,he⟩:=actual_cover_scalar τ hτ z
  have hi:=congrFun he i
  have hj':=congrFun he j
  change c*value τ hτ 3 i z=_ at hi
  change c*value τ hτ 3 j z=_ at hj'
  rw [←hi,←hj']
  field_simp [hc,hj]

@[expose] def pointEvaluation(z:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j z≠0):
    CoordinateChart τ hτ j→+*ℂ:=
  HomogeneousQuotientPointEvaluation318.evaluation (relations τ hτ)
    (baseVector τ hτ 1 (projection (P τ) z)) (relation_evaluation τ hτ _)
    j (actual_base_coordinate_nonzero τ hτ z j hj)
lemma pointEvaluation_scalar(z:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j z≠0)(c:ℂ):
    pointEvaluation τ hτ z j hj (algebraMap ℂ (CoordinateChart τ hτ j) c)=c:=by
  change pointEvaluation τ hτ z j hj (scalarMap τ hτ j c)=c
  rw [scalar_fraction]
  rw [pointEvaluation,HomogeneousQuotientPointEvaluation318.fraction_evaluation]
  simp only [MvPolynomial.eval_C,pow_zero,div_one]
@[expose] def algebraEvaluation(z:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j z≠0):
    CoordinateChart τ hτ j→ₐ[ℂ]ℂ:=
  {pointEvaluation τ hτ z j hj with commutes':=pointEvaluation_scalar τ hτ z j hj}

/-- Literal original coordinate ratio, with the same section-ring and
Scheme chart identifications already established. -/
@[expose] def ratioElement(j i:Label 3):CoordinateChart τ hτ j:=
  (quotientMap (relations τ hτ) j).rangeRestrict
    (fraction j 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i))
lemma ratio_is_original_section(j i:Label 3):ratioElement τ hτ j i=
    PELOriginalCandidateChartSections318.coordinates τ hτ j
      (PELOriginalCandidateChartSections318.ratioSection τ hτ j i):=by
  rw [PELOriginalCandidateChartSections318.ratioSection,
    PELOriginalCandidateChartSections318.coordinates_restriction]
  rfl
lemma actual_ratio_evaluation(z:ComplexVectors)(j i:Label 3)(hj:value τ hτ 3 j z≠0):
    algebraEvaluation τ hτ z j hj (ratioElement τ hτ j i)=
      value τ hτ 3 i z/value τ hτ 3 j z:=by
  change pointEvaluation τ hτ z j hj
    ((quotientMap (relations τ hτ) j).rangeRestrict (fraction j 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i)))=_
  rw [pointEvaluation,HomogeneousQuotientPointEvaluation318.fraction_evaluation]
  simp only [MvPolynomial.eval_X,pow_one]
  exact actual_base_ratio τ hτ z j i hj
end PELOriginalChartAnalyticEvaluation318
