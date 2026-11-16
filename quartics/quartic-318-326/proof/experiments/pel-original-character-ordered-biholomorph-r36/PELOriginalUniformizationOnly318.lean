module
public import CompactComplexRankTwoPeriods318
public section
noncomputable section
namespace PELOriginalUniformizationOnly318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalCharacterQuotient318 PELOriginalInvolutionComplexAtlas318
open PELOriginalUniformizedDoubling318 ComplexAffineFreeTranslation318
open scoped Manifold ContDiff
variable (i : Fin 4) (L : AddSubgroup ℂ) [DiscreteTopology L]
local instance : ChartedSpace ℂ (Torus L) := ComplexLineLatticeAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := ComplexLineLatticeAtlas318.complex_manifold L
local instance : ChartedSpace ℂ (CharacterBase i) :=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) :=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (InvolutionBase i) := involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i) := involution_manifold i
variable (u : InvolutionBase i ≃ₜ Torus L)

include u in
theorem quotient_compact : CompactSpace (Torus L) := by
  apply isCompact_univ_iff.mp
  rw [←Set.range_eq_univ.mpr u.surjective,←Set.image_univ]
  exact isCompact_univ.image u.continuous

/-- All integer periods are constructed from the actual compact curve;
rank two and a complete period basis are no longer separate hypotheses. -/
@[expose] def periods : RankTwoComplexHalfPeriods318.Coordinates ≃+ L := by
  letI := quotient_compact i L u
  exact CompactComplexRankTwoPeriods318.coordinates L

variable (hu : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u)
variable (huinv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u.symm)
@[expose] def character : CharacterBase i ≃ₜ Torus L :=
  characterComparison i L u (periods i L u) hu huinv

/-- Genuine original biholomorphic uniformization is the ONLY remaining
analytic producer. Original compactness constructs the rank-two lattice;
covering lifts and Liouville construct affine lifts; the actual free deck
maps exhaust two-torsion. The SAME torus factor is biholomorphic and the
original residual four-cover is exactly doubling. -/
theorem original_uniformization_only :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (character i L u hu huinv) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (character i L u hu huinv).symm ∧
    ∀ p,character i L u hu huinv (toCharacterBase i p)=(2:ℤ) • u p :=
  original_uniformized_doubling i L u (periods i L u) hu huinv
end PELOriginalUniformizationOnly318
