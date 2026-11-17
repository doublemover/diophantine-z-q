module
public import PELOriginalInvolutionActualTorus318
public import PELOriginalIndependentCubicComparison318
public section
noncomputable section
namespace PELOriginalProducedDoubling318
open ComplexAffineFreeTranslation318 PELOriginalInvolutionTower318 PELOriginalCharacterQuotient318
open scoped Topology Manifold ContDiff
variable (i:Fin 4)
abbrev L := PELOriginalInvolutionActualTorus318.periods i
local instance : ChartedSpace ℂ (Torus (L i)):=ComplexLineLatticeAtlas318.chartedSpace (L i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus (L i)):=ComplexLineLatticeAtlas318.complex_manifold (L i)
local instance : ChartedSpace ℂ (InvolutionBase i):=PELOriginalInvolutionComplexAtlas318.involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i):=PELOriginalInvolutionComplexAtlas318.involution_manifold i
local instance : ChartedSpace ℂ (CharacterBase i):=PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=PELOriginalCharacterComplexAtlas318.character_manifold i

/-- The formerly missing source uniformization is now the inverse of
the actual constructed whole-period quotient comparison. No new lattice,
rank, affine lift or source uniformization hypothesis is introduced. -/
@[expose] def source : InvolutionBase i≃ₜTorus (L i):=
  (PELOriginalInvolutionActualTorus318.comparison i).symm
lemma source_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (source i):=
  (PELOriginalInvolutionActualTorus318.biholomorphic i).2
lemma source_inverse_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (source i).symm:=
  (PELOriginalInvolutionActualTorus318.biholomorphic i).1

/-- The old actual deck/affine-lift argument now has every input
constructed. Its SAME-torus target comparison is not silently equated
with the earlier independently chosen modular-parameter coordinates. -/
@[expose] def character : CharacterBase i≃ₜTorus (L i):=
  PELOriginalUniformizationOnly318.character i (L i) (source i)
    (source_holomorphic i) (source_inverse_holomorphic i)
theorem constructed_doubling :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (character i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (character i).symm ∧
    ∀p,character i (toCharacterBase i p)=(2:ℤ) • source i p :=
  PELOriginalUniformizationOnly318.original_uniformization_only i (L i) (source i)
    (source_holomorphic i) (source_inverse_holomorphic i)

/-- All source periods have an actual complete rank-two integer basis,
not just two independent candidates. -/
@[expose] def integerPeriods : RankTwoComplexHalfPeriods318.Coordinates≃+L i:=
  CompactComplexRankTwoPeriods318.coordinates (L i)
lemma rank_two : Module.finrank ℤ (CompactComplexRankTwoPeriods318.integerModule (L i))=2:=
  CompactComplexRankTwoPeriods318.rank_two (L i)

@[expose] def sourcePoints : InvolutionBase i≃(OriginalPeriodEllipticPoints318.curve (L i)).toAffine.Point:=
  PELOriginalAlgebraicDoubling318.involutionPoints i (L i) (source i)
@[expose] def characterPoints : CharacterBase i≃(OriginalPeriodEllipticPoints318.curve (L i)).toAffine.Point:=
  PELOriginalAlgebraicDoubling318.characterPoints i (L i) (source i)
    (source_holomorphic i) (source_inverse_holomorphic i)

/-- The ORIGINAL residual four-cover is now unconditionally identified
with native algebraic elliptic doubling on the SAME original full-period
curve, not merely with some abstract degree-four isogeny. -/
theorem native_doubling (p:InvolutionBase i) :
    characterPoints i (toCharacterBase i p)=sourcePoints i p+sourcePoints i p:=
  PELOriginalAlgebraicDoubling318.original_algebraic_doubling i (L i) (source i)
    (source_holomorphic i) (source_inverse_holomorphic i) p
end PELOriginalProducedDoubling318
