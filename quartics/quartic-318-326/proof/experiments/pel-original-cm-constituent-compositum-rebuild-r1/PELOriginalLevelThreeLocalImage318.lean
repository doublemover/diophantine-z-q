module
public import PELOriginalLevelThetaStrictDerivative318
public import SplitHolomorphicImage318
public import PELOriginalLevelThreeClosedEmbedding318
public section
noncomputable section
namespace PELOriginalLevelThreeLocalImage318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLevelThetaStrictDerivative318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open DiscreteComplexPeriodAtlas318 ComplexProjectiveComplexAtlas318
open Filter Topology Set
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=
  PELOriginalPeriodLattice318.original_discrete τ hτ

@[expose] def localProjection (x:ComplexVectors) (j:Label 3):
    TargetModel 1→L[ℂ]ComplexVectors:=
  SplitHolomorphicImage318.projection (fderiv ℂ (ratioVector τ hτ 1 j) x)
@[expose] def parameterChart (x:ComplexVectors) (j:Label 3)
    (hj:value τ hτ 3 j x≠0):OpenPartialHomeomorph ComplexVectors ComplexVectors:=
  SplitHolomorphicImage318.chart (ratioVector τ hτ 1 j) x
    (ratio_contDiffAt τ hτ 1 j x hj)
    (PELOriginalLevelThreeTangentSeparation318.chart_derivative_injective τ hτ x j hj)
@[expose] def imageGraph (x:ComplexVectors) (j:Label 3)
    (hj:value τ hτ 3 j x≠0):ComplexVectors→TargetModel 1:=
  SplitHolomorphicImage318.graph (ratioVector τ hτ 1 j) x
    (ratio_contDiffAt τ hτ 1 j x hj)
    (PELOriginalLevelThreeTangentSeparation318.chart_derivative_injective τ hτ x j hj)
lemma parameterChart_center (x:ComplexVectors) (j:Label 3)
    (hj:value τ hτ 3 j x≠0):x∈(parameterChart τ hτ x j hj).source:=
  SplitHolomorphicImage318.center_mem _ _ _ _
lemma actual_original_formula (x:ComplexVectors) (j:Label 3) (z:ComplexVectors):
    ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j
      (projectiveMap τ hτ 1 ((DiscreteComplexPeriodAtlas318.localChart (P τ) x).symm z))=
      ratioVector τ hτ 1 j z:=
  PELOriginalLevelThreeTangentSeparation318.original_chart_representation τ hτ x j z

@[expose] def originalChartDomain (x:ComplexVectors) (j:Label 3):Set ComplexVectors:=
  (DiscreteComplexPeriodAtlas318.localChart (P τ) x).target ∩
    {z|value τ hτ 3 j z≠0}
lemma originalChartDomain_open (x:ComplexVectors) (j:Label 3):
    IsOpen (originalChartDomain τ hτ x j):=
  (DiscreteComplexPeriodAtlas318.localChart (P τ) x).open_target.inter
    (isOpen_ne (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous
      continuous_const)
lemma originalChartDomain_center (x:ComplexVectors) (j:Label 3)
    (hj:value τ hτ 3 j x≠0):x∈originalChartDomain τ hτ x j:=by
  refine ⟨?_,hj⟩
  have h:=(DiscreteComplexPeriodAtlas318.localChart (P τ) x).map_source
    (DiscreteComplexPeriodAtlas318.localChart_center (P τ) x)
  have hv:(DiscreteComplexPeriodAtlas318.localChart (P τ) x) (projection (P τ) x)=x:=
    (DiscreteComplexPeriodAtlas318.quotient_localHomeomorph (P τ)).localInverseAt_apply_self
  rwa [hv] at h

/-- In every genuine nonzero homogeneous chart, the original level-three
map has an explicitly constructed holomorphic local graph, whose inverse
is the actual continuous complex-linear derivative projection. -/
theorem local_holomorphic_image (x:ComplexVectors) (j:Label 3)
    (hj:value τ hτ 3 j x≠0):
    ∃W:Set ComplexVectors,IsOpen W ∧
      localProjection τ hτ x j (ratioVector τ hτ 1 j x)∈W ∧
      W⊆(parameterChart τ hτ x j hj).target ∧
      DifferentiableOn ℂ (imageGraph τ hτ x j hj) W ∧
      (∀w∈W,(parameterChart τ hτ x j hj).symm w∈originalChartDomain τ hτ x j) ∧
      (∀w∈W,localProjection τ hτ x j (imageGraph τ hτ x j hj w)=w) ∧
      ratioVector τ hτ 1 j ''
        ((parameterChart τ hτ x j hj).source ∩
          (fun z=>localProjection τ hτ x j (ratioVector τ hτ 1 j z)) ⁻¹' W)=
        imageGraph τ hτ x j hj '' W:=
  SplitHolomorphicImage318.exists_holomorphic_graph (ratioVector τ hτ 1 j) x
    (ratio_contDiffAt τ hτ 1 j x hj)
    (PELOriginalLevelThreeTangentSeparation318.chart_derivative_injective τ hτ x j hj)
    (originalChartDomain τ hτ x j) (originalChartDomain_open τ hτ x j)
    (originalChartDomain_center τ hτ x j hj)

/-- No choice of a suitable target chart is an additional premise: the
actual original finite family has no common zero. This is an analytic
local-image result; rational/algebraic descent is not inferred. -/
theorem every_original_point (x:ComplexVectors):
    ∃j:Label 3,∃hj:value τ hτ 3 j x≠0,
      x∈(parameterChart τ hτ x j hj).source ∧
      HasStrictFDerivAt (ratioVector τ hτ 1 j)
        (fderiv ℂ (ratioVector τ hτ 1 j) x) x ∧
      Function.Injective (fderiv ℂ (ratioVector τ hτ 1 j) x):=by
  have hn:=coverVector_nonzero τ hτ 1 x
  have he:∃j:Label 3,value τ hτ 3 j x≠0:=by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨j,hj⟩:=he
  exact ⟨j,hj,parameterChart_center τ hτ x j hj,
    level_three_strict_injective τ hτ j x hj⟩
end PELOriginalLevelThreeLocalImage318
