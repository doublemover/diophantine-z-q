module
public import PELOriginalFourThetaHolomorphicMap318
public section
noncomputable section
namespace PELOriginalFourThetaOriginDerivative318
open QuaternionicRealPeriod318 Filter Topology
open PELOriginalFourThetaProjectiveMap318 PELOriginalFourThetaHolomorphicMap318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationTransitions318 ComplexProjectiveQuotientTopology318

/-- An even differentiable map has zero full complex Frechet derivative
at the origin. This is not merely a directional derivative assertion. -/
lemma even_derivative_zero {E F:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
    [NormedAddCommGroup F][NormedSpace ℂ F](f:E→F)
    (hf:DifferentiableAt ℂ f 0)(heven:∀z,f (-z)=f z):fderiv ℂ f 0=0:=by
  have hn:HasFDerivAt (fun z:E=>f (-z))
      ((fderiv ℂ f 0).comp (-ContinuousLinearMap.id ℂ E)) 0:=by
    simpa only [neg_zero] using hf.hasFDerivAt.comp 0 (hasFDerivAt_id (0:E)).neg
  have he:(fderiv ℂ f 0).comp (-ContinuousLinearMap.id ℂ E)=fderiv ℂ f 0:=
    (hn.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z=>(heven z).symm))).unique hf.hasFDerivAt
  ext v
  have hv:=congrArg (fun A:E→L[ℂ]F=>A v) he
  have hneg: -(fderiv ℂ f 0 v)=fderiv ℂ f 0 v:=by
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply,map_neg] using hv
  have htwo:(2:ℂ) • (fderiv ℂ f 0 v)=0:=by
    simpa only [two_smul] using (neg_eq_iff_add_eq_zero.mp hneg)
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

variable (τ:ℂ)(hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=
  PELOriginalPeriodLattice318.original_discrete τ hτ

/-- The ratio map is literally the original map expressed in the genuine
source chart centered at zero and the actual target projective chart. -/
lemma original_chart_representation(j:Label 2)(z:ComplexVectors):
    ComplexProjectiveComplexAtlas318.localChart (Label 2) 0 j
      (projectiveMap τ hτ ((DiscreteComplexPeriodAtlas318.localChart (P τ) 0).symm z))=
      ratioVector τ hτ j z:=by
  rw [DiscreteComplexPeriodAtlas318.localChart_symm,original_covering_square]
  exact actual_ratio τ hτ j z
lemma ratio_even(j:Label 2)(z:ComplexVectors):
    ratioVector τ hτ j (-z)=ratioVector τ hτ j z:=by
  unfold ratioVector
  congr 1
  funext i
  rw [value_even,value_even]

/-- In EVERY genuine target affine chart containing the original origin
image, the actual local projective map has zero full derivative there. -/
theorem actual_origin_ratio_derivative(j:Label 2)(hj:value τ hτ 2 j 0≠0):
    fderiv ℂ (ratioVector τ hτ j) 0=0:=
  even_derivative_zero _ (ratio_differentiable τ hτ j 0 hj) (ratio_even τ hτ j)

/-- A valid actual target chart exists at the origin by the constructed
four-section generation theorem; derivative vanishing is not vacuous. -/
theorem actual_origin_chart_critical:
    ∃j:Label 2,value τ hτ 2 j 0≠0 ∧
      fderiv ℂ (ratioVector τ hτ j) 0=0:=by
  have hn:=coverVector_nonzero τ hτ (0:ComplexVectors)
  have he:∃j:Label 2,value τ hτ 2 j 0≠0:=by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨j,hj⟩:=he
  exact ⟨j,hj,actual_origin_ratio_derivative τ hτ j hj⟩

/-- Explicit failure of tangent injectivity in actual local projective
coordinates of the original map. The source covering is its genuine
local period chart, not a replacement parameter space. Thus the level-two
map cannot supply the required projective immersion of the surface. -/
theorem actual_origin_ratio_not_injective(j:Label 2)(hj:value τ hτ 2 j 0≠0):
    ¬Function.Injective (fderiv ℂ (ratioVector τ hτ j) 0):=by
  rw [actual_origin_ratio_derivative τ hτ j hj]
  intro hinj
  have he:(![1,0]:ComplexVectors)=0:=hinj rfl
  have h:=congrFun he (0:Fin 2)
  norm_num at h
end PELOriginalFourThetaOriginDerivative318
