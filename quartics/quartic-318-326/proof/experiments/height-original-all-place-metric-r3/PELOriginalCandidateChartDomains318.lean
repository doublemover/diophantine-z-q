module
public import PELOriginalCandidateIntegral318
public section
noncomputable section
namespace PELOriginalCandidateChartDomains318
open AlgebraicGeometry CategoryTheory
open PELOriginalCubicRelationIdeal318 PELOriginalReducedProjectiveCandidate318
open PELOriginalCandidateIntegral318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateChartSections318 PELOriginalLevelTheta318
open PELOriginalWholeHZeroDimension318 PELOriginalGradedSectionRing318
variable (τ:ℂ)(hτ:0<τ.im)

/-- Every original cubic coordinate is genuinely nonzero, by the proved
independence of the actual nine sections. This is not inferred merely
from the absence of a common zero of the family. -/
lemma variable_not_relation(j:Label 3):MvPolynomial.X j∉relations τ hτ:=by
  intro h
  have hg:generators τ hτ j=0:=by
    change presentation τ hτ (MvPolynomial.X j)=0 at h
    rwa [variable_image] at h
  have hv:thetaVector τ hτ 3 j=0:=by
    apply include_injective τ hτ 3
    simpa only [map_zero,generators] using hg
  apply (PELOriginalLevelPowerSections318.sections_independent τ hτ 3).ne_zero j
  exact congrArg Subtype.val hv

lemma generic_in_every_chart(j:Label 3):genericPoint τ hτ∈ambientChart j:=by
  change MvPolynomial.X j∉relations τ hτ
  exact variable_not_relation τ hτ j
lemma chart_nonempty(j:Label 3):Nonempty (candidateChart τ hτ j).toScheme:=by
  have hg:genericPoint τ hτ∈Set.range (inclusion τ hτ):=by
    rw [inclusion_range,zeroSet_generic]
    exact subset_closure (Set.mem_singleton _)
  obtain ⟨x,hx⟩:=hg
  refine ⟨⟨x,?_⟩⟩
  change inclusion τ hτ x∈ambientChart j
  rw [hx]
  exact generic_in_every_chart τ hτ j

/-- Every original affine coordinate chart is integral, not merely a
possibly empty reduced closed subscheme. The actual generic point lies
in ALL nine charts because each original cubic section is nonzero. -/
theorem chart_integral(j:Label 3):IsIntegral (candidateChart τ hτ j).toScheme:=by
  haveI:IsIntegral (candidate τ hτ):=integral τ hτ
  haveI:Nonempty (candidateChart τ hτ j).toScheme:=chart_nonempty τ hτ j
  exact isIntegral_of_isOpenImmersion (candidateChart τ hτ j).ι

theorem coordinate_chart_domain(j:Label 3):IsDomain (CoordinateChart τ hτ j):=by
  haveI:IsIntegral (candidateChart τ hτ j).toScheme:=chart_integral τ hτ j
  exact (coordinates τ hτ j).toMulEquiv.isDomain _
end PELOriginalCandidateChartDomains318
