module
public import OriginalPeriodWeierstrassHolomorphy318
public section
noncomputable section
namespace PELOriginalWeierstrassCoordinates318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalCharacterQuotient318 PELOriginalInvolutionComplexAtlas318
open PELOriginalUniformizationOnly318 ComplexAffineFreeTranslation318
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

@[expose] def periods : PeriodPair := OriginalComplexPeriodPair318.pair L
@[expose] def origin : InvolutionBase i := u.symm 0
@[expose] def originalX (p : InvolutionBase i) : ℂ := OriginalPeriodWeierstrassCoordinates318.x L (u p)
@[expose] def originalY (p : InvolutionBase i) : ℂ := OriginalPeriodWeierstrassCoordinates318.y L (u p)

/-- Actual coordinates on the original involution curve satisfy the
cubic with genuine full-period lattice sums, away from the chosen origin.
No published equation or j invariant is assumed. -/
theorem original_cubic (p : InvolutionBase i) (hp : p≠origin i L u) :
    originalY i L u p ^ 2=4*originalX i L u p ^ 3-
      (periods i L u).g₂*originalX i L u p-(periods i L u).g₃ := by
  apply OriginalPeriodWeierstrassCoordinates318.cubic L (u p)
  intro h
  apply hp
  exact u.injective (h.trans (u.apply_symm_apply 0).symm)

variable (hu : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u)
variable (huinv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u.symm)

include hu in
theorem original_holomorphicAt (p : InvolutionBase i) (hp : p≠origin i L u) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (originalX i L u) p ∧
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (originalY i L u) p := by
  have hn : u p≠0 := by
    intro h
    exact hp (u.injective (h.trans (u.apply_symm_apply 0).symm))
  exact ⟨(OriginalPeriodWeierstrassHolomorphy318.x_holomorphicAt L (u p) hn).comp p (hu p),
    (OriginalPeriodWeierstrassHolomorphy318.y_holomorphicAt L (u p) hn).comp p (hu p)⟩

@[expose] def characterX (q : CharacterBase i) : ℂ :=
  OriginalPeriodWeierstrassCoordinates318.x L (character i L u hu huinv q)
@[expose] def characterY (q : CharacterBase i) : ℂ :=
  OriginalPeriodWeierstrassCoordinates318.y L (character i L u hu huinv q)

theorem character_cubic (q : CharacterBase i) (hq : character i L u hu huinv q≠0) :
    characterY i L u hu huinv q ^ 2=4*characterX i L u hu huinv q ^ 3-
      (periods i L u).g₂*characterX i L u hu huinv q-(periods i L u).g₃ :=
  OriginalPeriodWeierstrassCoordinates318.cubic L _ hq

/-- The original four-cover acts on these SAME actual cubic coordinate
functions by the already constructed torus doubling, not a fresh isogeny. -/
theorem original_cover_coordinate_square (p : InvolutionBase i) :
    characterX i L u hu huinv (toCharacterBase i p)=
      OriginalPeriodWeierstrassCoordinates318.x L ((2:ℤ) • u p) ∧
    characterY i L u hu huinv (toCharacterBase i p)=
      OriginalPeriodWeierstrassCoordinates318.y L ((2:ℤ) • u p) := by
  have h := (original_uniformization_only i L u hu huinv).2.2 p
  exact ⟨congrArg (OriginalPeriodWeierstrassCoordinates318.x L) h,
    congrArg (OriginalPeriodWeierstrassCoordinates318.y L) h⟩
end PELOriginalWeierstrassCoordinates318
