module
public import PELOriginalProducedDoubling318
public section
noncomputable section
namespace PELOriginalProducedPeriodCubic318
open PELOriginalProducedDoubling318 PELOriginalInvolutionTower318 PELOriginalCharacterQuotient318
open scoped Topology Manifold ContDiff
variable (i:Fin 4)
local instance : ChartedSpace ℂ (InvolutionBase i):=PELOriginalInvolutionComplexAtlas318.involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i):=PELOriginalInvolutionComplexAtlas318.involution_manifold i
local instance : ChartedSpace ℂ (CharacterBase i):=PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (OriginalPeriodPlaneOverlap318.CompletedPlane (L i)):=
  OriginalPeriodCompletedComplexAtlas318.chartedSpace (L i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OriginalPeriodPlaneOverlap318.CompletedPlane (L i)):=
  OriginalPeriodCompletedComplexAtlas318.complex_manifold (L i)

/-- The actual original involution curve is compared to an independently
constructed smooth proper projective cubic with its genuine full-period
coefficients. Original curve uniformization is no longer an input. -/
@[expose] def involution : InvolutionBase i≃ₜOriginalPeriodPlaneOverlap318.CompletedPlane (L i):=
  PELOriginalIndependentCubicComparison318.involution i (L i) (source i)
@[expose] def character : CharacterBase i≃ₜOriginalPeriodPlaneOverlap318.CompletedPlane (L i):=
  PELOriginalIndependentCubicComparison318.characterComparison i (L i) (source i)
    (source_holomorphic i) (source_inverse_holomorphic i)
lemma involution_biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (involution i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (involution i).symm :=
  PELOriginalIndependentCubicComparison318.involution_biholomorphic i (L i) (source i)
    (source_holomorphic i) (source_inverse_holomorphic i)
lemma character_biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (character i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (character i).symm :=
  PELOriginalIndependentCubicComparison318.character_biholomorphic i (L i) (source i)
    (source_holomorphic i) (source_inverse_holomorphic i)
lemma source_scheme (p:InvolutionBase i) :
    OriginalPeriodCompletedPointIdentification318.schemeEquivalence (L i) (involution i p)=
      OriginalPeriodCompletedSchemeBijection318.nativeEquivalence (L i) (sourcePoints i p) :=
  PELOriginalIndependentCubicComparison318.involution_scheme i (L i) (source i) p
lemma character_scheme (p:CharacterBase i) :
    OriginalPeriodCompletedPointIdentification318.schemeEquivalence (L i) (character i p)=
      OriginalPeriodCompletedSchemeBijection318.nativeEquivalence (L i) (characterPoints i p) :=
  PELOriginalIndependentCubicComparison318.character_scheme i (L i) (source i)
    (source_holomorphic i) (source_inverse_holomorphic i) p

/-- Same original residual map, same independently constructed native
elliptic group and actual ALL-scheme-points identification, including
infinity. Algebraization to a scheme morphism and published coefficient
identification remain separate from this proved analytic/point square. -/
theorem actual_residual_scheme_square (p:InvolutionBase i) :
    OriginalPeriodCompletedPointIdentification318.schemeEquivalence (L i)
      (character i (toCharacterBase i p))=
      OriginalPeriodCompletedSchemeBijection318.nativeEquivalence (L i)
        (sourcePoints i p+sourcePoints i p) := by
  rw [character_scheme,native_doubling]
end PELOriginalProducedPeriodCubic318
