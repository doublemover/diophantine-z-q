module
public import AdmissibleJComplexAtlas318
public import ActualJSurjective318
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public section
noncomputable section
open scoped Manifold ContDiff
namespace AdmissiblePeriodProjection318
open ModularArithmeticCoordinates318 ThreeArithmeticQuotient318
open AdmissibleJLocalHomeomorph318 OpenJLocalComparison318
set_option maxHeartbeats 500000

/-- Nonemptiness is supplied by the actual genuine j-surjectivity theorem,
not an extra assumption on the admissible period locus. -/
theorem locus_nonempty : Nonempty Locus := by
  obtain ⟨tau,htau⟩:=ActualJSurjective318.surjective (1:ℂ)
  refine ⟨⟨tau,?_⟩⟩
  change ActualQJ318.jInvariant tau≠0 ∧ ActualQJ318.jInvariant tau≠1728
  rw [htau]
  norm_num

local instance : Nonempty Locus := locus_nonempty

/-- The usual complex open-subspace atlas, using literal period inclusion.
This definition does not use the quotient or its j charts. -/
@[expose, instance_reducible] def complexChartedSpace : ChartedSpace ℂ Locus :=
  locus_complex_embedding.singletonChartedSpace

lemma chart_apply (tau sigma : Locus) :
    letI:=complexChartedSpace
    chartAt ℂ tau sigma=(sigma.val:ℂ) := rfl

theorem complex_manifold : letI:=complexChartedSpace; IsManifold 𝓘(ℂ) ω Locus := by
  letI:=complexChartedSpace
  exact locus_complex_embedding.isManifold_singleton

/-- Literal period inclusion is analytic in the independently defined
open-subspace complex structure. -/
theorem inclusion_analytic :
    letI:=complexChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun tau : Locus=>(tau.val:ℂ)) := by
  letI:=complexChartedSpace
  exact contMDiff_isOpenEmbedding locus_complex_embedding

/-- Genuine j remains analytic on the actual natural complex period locus. -/
theorem periodJ_analytic :
    letI:=complexChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun tau:Locus=>ActualQJ318.jInvariant tau.val) := by
  letI:=complexChartedSpace
  intro tau
  have h:=(j_analyticAt tau.val).contDiffAt.comp_contMDiffAt
    (f := fun sigma : Locus => (sigma.val : ℂ)) (x := tau) (inclusion_analytic tau)
  simpa only [Function.comp_def,j,UpperHalfPlane.ofComplex_apply] using h

/-- The actual period-to-orbit projection is analytic for the natural
period complex structure and the exact genuine-j source atlas. Its proof
uses actual j-analyticity, not covering-space topology alone. -/
theorem sourceProjection_analytic :
    letI:=complexChartedSpace
    letI:=AdmissibleJComplexAtlas318.complexChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω sourceProjection := by
  letI:=complexChartedSpace
  letI:=AdmissibleJComplexAtlas318.complexChartedSpace
  intro tau
  apply contMDiffAt_iff_target.mpr
  refine ⟨sourceProjection_isOpenQuotientMap.isQuotientMap.continuous.continuousAt,?_⟩
  have he:(extChartAt 𝓘(ℂ) (sourceProjection tau) ∘ sourceProjection)=
      (fun sigma:Locus=>ActualQJ318.jInvariant sigma.val) := by
    funext sigma
    change AdmissibleJComplexAtlas318.localChart (sourceProjection tau)
      (sourceProjection sigma)=ActualQJ318.jInvariant sigma.val
    rw [AdmissibleJComplexAtlas318.localChart_apply,sourceComplexJ_projection]
  rw [he]
  exact periodJ_analytic tau

end AdmissiblePeriodProjection318
