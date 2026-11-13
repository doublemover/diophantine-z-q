module
public import ComplexLineAffineLifts318
public section
noncomputable section
namespace PELOriginalAffineDeckProducer318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalInvolutionComplexAtlas318 PELOriginalResidualDeckAction318
open PELOriginalResidualDeckHolomorphy318 PELOriginalDeckTwoTorsion318
open PELOriginalDoublingHolomorphy318 ComplexAffineFreeTranslation318
open scoped Manifold ContDiff
set_option maxHeartbeats 3000000
variable (i : Fin 4) (L : AddSubgroup ℂ) [DiscreteTopology L]
local instance : ChartedSpace ℂ (Torus L) := ComplexLineLatticeAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := ComplexLineLatticeAtlas318.complex_manifold L
local instance : ChartedSpace ℂ (InvolutionBase i) := involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i) := involution_manifold i
variable (u : InvolutionBase i ≃ₜ Torus L)

/-- Affine lifts of the ORIGINAL deck action are now constructed from
biholomorphic uniformization, original compactness and the actual deck
holomorphy. No affine-lift premise remains. -/
theorem original_affine_lifts
    (hu : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u)
    (huinv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u.symm) : AffineLifts i L u.toEquiv := by
  letI : CompactSpace (Torus L) := by
    apply isCompact_univ_iff.mp
    rw [←Set.range_eq_univ.mpr u.surjective,←Set.image_univ]
    exact isCompact_univ.image u.continuous
  intro g
  have hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun z : Torus L => u (g • u.symm z)) :=
    hu.comp ((deck_holomorphic i g).comp huinv)
  exact ComplexLineAffineLifts318.holomorphic_affine_lift L _ hf
end PELOriginalAffineDeckProducer318
