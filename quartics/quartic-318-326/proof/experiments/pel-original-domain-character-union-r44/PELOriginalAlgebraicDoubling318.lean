module
public import OriginalPeriodEllipticGroup318
public section
noncomputable section
namespace PELOriginalAlgebraicDoubling318
open PELOriginalInvolutionTower318 PELOriginalCharacterQuotient318
open PELOriginalInvolutionComplexAtlas318 PELOriginalUniformizationOnly318
open ComplexAffineFreeTranslation318 OriginalPeriodEllipticPoints318
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
local instance : CompactSpace (Torus L) := quotient_compact i L u

/-- Original involution points correspond to native points of the
independently constructed algebraic period curve, including its infinity. -/
@[expose] def involutionPoints : InvolutionBase i ≃ (curve L).toAffine.Point :=
  u.toEquiv.trans (equivalence L)

variable (hu : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u)
variable (huinv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u.symm)
@[expose] def characterPoints : CharacterBase i ≃ (curve L).toAffine.Point :=
  (character i L u hu huinv).toEquiv.trans (equivalence L)

/-- The original residual degree-four map is exactly multiplication by
TWO in the NATIVE elliptic-curve group, not merely doubling in an abstract
transported torus group or an arbitrary isogenous elliptic curve. -/
theorem original_algebraic_doubling (p : InvolutionBase i) :
    characterPoints i L u hu huinv (toCharacterBase i p)=
      involutionPoints i L u p+involutionPoints i L u p := by
  change point L (character i L u hu huinv (toCharacterBase i p))=
    point L (u p)+point L (u p)
  rw [(original_uniformization_only i L u hu huinv).2.2 p]
  simpa only [two_zsmul] using OriginalPeriodEllipticGroup318.point_add L (u p) (u p)
end PELOriginalAlgebraicDoubling318
