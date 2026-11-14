module
public import PELEffectiveNormOneAction318
public section
noncomputable section
namespace PELUnlevelledComplexBase318
open QuaternionicJointPeriodTopology318 PELJointPeriodDeck318 PELJointNormOneAction318
open PELPrincipalThreeFreeAction318 PELPrincipalThreeCovering318 PELPrincipalBaseHolomorphy318
open PELArithmeticComplexFamily318 PELJointComplexAtlas318 PELEffectiveNormOneAction318
open HolomorphicQuotientCoverCharts318 HolomorphicQuotientCoverMaps318
open scoped Manifold ContDiff
set_option maxHeartbeats 1500000
local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold
local instance : LocallyCompactSpace HalfPlane := (baseChart.isOpenEmbedding rfl).locallyCompactSpace

/-- The literal unlevelled norm-one quotient on the chosen positive
component. It is not yet identified with an algebraic Shimura/contact curve. -/
abbrev UnlevelledBase := Quotient (MulAction.orbitRel effectiveGroup HalfPlane)
@[expose] def projection : HalfPlane → UnlevelledBase := Quotient.mk _

theorem covering : IsQuotientCoveringMap projection effectiveGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem projection_surjective : Function.Surjective projection := Quotient.mk_surjective

@[expose,instance_reducible] def unlevelledCharts : ChartedSpace ℂ UnlevelledBase :=
  quotientCharts projection covering

theorem unlevelled_manifold :
    letI := unlevelledCharts
    IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase :=
  quotient_manifold projection covering effective_holomorphic

local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
local instance : ChartedSpace ℂ ArithmeticBase := arithmeticBaseCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω ArithmeticBase := arithmeticBase_manifold

theorem projection_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω projection :=
  HolomorphicQuotientCoverMaps318.projection_holomorphic projection covering effective_holomorphic

/-- Forgetting principal-three level is an actual quotient map, with the
same source parameter and full original orbit relation. -/
@[expose] def forgetLevel : ArithmeticBase → UnlevelledBase :=
  Quotient.map' id (by
    rintro τ σ ⟨u,hu⟩
    exact ⟨effectiveMap ⟨u.val,u.property.1⟩,hu⟩)

theorem forgetLevel_square (τ : HalfPlane) : forgetLevel (baseQuotient τ)=projection τ := rfl

theorem forgetLevel_surjective : Function.Surjective forgetLevel := by
  intro x
  obtain ⟨τ,rfl⟩ := projection_surjective x
  exact ⟨baseQuotient τ,rfl⟩

theorem forgetLevel_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω forgetLevel :=
  descended_holomorphic baseQuotient base_covering principal_base_holomorphic
    forgetLevel projection projection_holomorphic forgetLevel_square
end PELUnlevelledComplexBase318
