module
public import PELOriginalAffineDeckProducer318
public section
noncomputable section
namespace PELOriginalUniformizedDoubling318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalCharacterQuotient318 PELOriginalInvolutionComplexAtlas318
open PELOriginalDoublingTopology318 PELOriginalDoublingHolomorphy318
open PELOriginalAffineDeckProducer318 ComplexAffineFreeTranslation318
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
variable (basis : RankTwoComplexHalfPeriods318.Coordinates ≃+ L)
variable (hu : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u)
variable (huinv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u.symm)

/-- The actual character quotient is identified with the SAME uniformizing
period torus, with every affine-lift and deck-translation input constructed. -/
@[expose] def characterComparison : CharacterBase i ≃ₜ Torus L :=
  characterHomeomorph i L u basis (original_affine_lifts i L u hu huinv)

/-- Only genuine uniformization of the original involution curve and its
rank-two periods remain as inputs. The residual map, original deck lifts,
all two-torsion, exact doubling identity and both holomorphies are produced. -/
theorem original_uniformized_doubling :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (characterComparison i L u basis hu huinv) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (characterComparison i L u basis hu huinv).symm ∧
    ∀ p,characterComparison i L u basis hu huinv (toCharacterBase i p)=(2:ℤ) • u p :=
  original_biholomorphic_doubling i L u basis
    (original_affine_lifts i L u hu huinv) hu huinv
end PELOriginalUniformizedDoubling318
