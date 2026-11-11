module
public import PELDirichletOrbitBound318
public import PELMaximalQuotientProper318
public section
noncomputable section
namespace PELOriginalBaseCompact318
open QuaternionicJointPeriodTopology318 PELJointNormOneAction318 PELUnlevelledComplexBase318
open PELDirichletHeight318 PELHeightCompactSublevels318 PELDirichletOrbitBound318
open PELEffectiveNormOneAction318
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : ChartedSpace ℂ HalfPlane := PELPrincipalBaseHolomorphy318.halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := PELPrincipalBaseHolomorphy318.halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

theorem projection_unit (u : normOneUnits) (τ : HalfPlane) :
    projection (u • τ)=projection τ :=
  Quotient.sound ⟨effectiveMap u,effectiveMap_action u τ⟩

/-- Every point of the literal original arithmetic quotient is the image
of the explicitly bounded original upper-half-plane subset. -/
theorem compact_domain_covers : projection '' {τ : HalfPlane | height τ≤200}=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨τ,rfl⟩ := projection_surjective x
  obtain ⟨u,hu⟩ := original_orbit_reduction τ
  exact ⟨u • τ,hu,projection_unit u τ⟩

/-- Cocompactness of the actual original norm-one arithmetic quotient,
constructed from exact units, proper discontinuity and rational inequalities. -/
instance original_unlevelled_compact : CompactSpace UnlevelledBase := by
  apply isCompact_univ_iff.mp
  rw [← compact_domain_covers]
  exact (sublevel_compact 200 (by norm_num)).image projection_holomorphic.continuous

/-- The actual full-positive-normalizer quotient is compact as the
continuous image of the same original compact arithmetic curve. -/
instance original_maximal_compact : CompactSpace PELOriginalMaximalQuotient318.MaximalBase := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr PELOriginalMaximalQuotient318.projection_surjective,
    ← Set.image_univ]
  exact isCompact_univ.image PELOriginalMaximalQuotient318.projection_continuous
end PELOriginalBaseCompact318
