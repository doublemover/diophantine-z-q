module
public import LegendreActualTorus318
public import PELOriginalCompletedBiholomorph318
public section
noncomputable section
namespace PELOriginalCharacterTorus318
open ComplexAffineFreeTranslation318 PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open scoped Topology Manifold ContDiff
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
@[expose] def periods : AddSubgroup ℂ:=LegendreActualTorus318.periods (branchParameter i)
instance periods_discrete : DiscreteTopology (periods i):=
  LegendreActualTorus318.periods_discrete (branchParameter i)
instance quotient_compact : CompactSpace (Torus (periods i)):=
  LegendreActualTorus318.quotient_compact (branchParameter i)
local instance : ChartedSpace ℂ (Torus (periods i)):=ComplexLineLatticeAtlas318.chartedSpace (periods i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus (periods i)):=ComplexLineLatticeAtlas318.complex_manifold (periods i)
local instance : ChartedSpace ℂ (CharacterBase i):=PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (LegendrePlaneOverlap318.CompletedPlane (branchParameter i)):=
  LegendreCompletedComplexAtlas318.chartedSpace (branchParameter i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (LegendrePlaneOverlap318.CompletedPlane (branchParameter i)):=
  LegendreCompletedComplexAtlas318.complex_manifold (branchParameter i)

/-- Actual period uniformization of the ORIGINAL character quotient.
The period subgroup, discreteness, compact quotient and both holomorphic
maps are all constructed, not new assumptions on this endpoint. -/
@[expose] def comparison : Torus (periods i)≃ₜCharacterBase i :=
  (LegendreActualTorus318.comparison (branchParameter i)).trans
    (PELOriginalCompletedBiholomorph318.comparison i).symm
theorem biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison i).symm :=
  ⟨(PELOriginalCompletedBiholomorph318.inverse_holomorphic i).comp
      (LegendreActualTorus318.biholomorphic (branchParameter i)).1,
    (LegendreActualTorus318.biholomorphic (branchParameter i)).2.comp
      (PELOriginalCompletedBiholomorph318.forward_holomorphic i)⟩
lemma actual_completed (q:Torus (periods i)) :
    PELOriginalCompletedBiholomorph318.comparison i (comparison i q)=
      LegendreActualTorus318.comparison (branchParameter i) q :=
  (PELOriginalCompletedBiholomorph318.comparison i).apply_symm_apply _
lemma actual_projection (q:Torus (periods i)) :
    PELOriginalCommonLegendreBase318.originalProjection i (comparison i q)=
      NormalizedLegendreFiniteProjection318.project (branchParameter i)
        (LegendreCompletedPointIdentification318.schemeEquivalence (branchParameter i)
          (LegendreActualTorus318.comparison (branchParameter i) q)) := by
  rw [←actual_completed,PELOriginalCompletedBiholomorph318.actual_projection]
end PELOriginalCharacterTorus318
