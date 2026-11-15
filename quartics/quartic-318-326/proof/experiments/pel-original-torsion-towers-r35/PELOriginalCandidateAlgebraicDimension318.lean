module
public import PELOriginalChartKrullDimension318
public import SoberOpenCoverDimension318
public import PELOriginalCandidateNineChartCover318
public import PELOriginalProperSmoothGroup318
public section
noncomputable section
namespace PELOriginalCandidateAlgebraicDimension318
open AlgebraicGeometry CategoryTheory
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalReducedProjectiveCandidate318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0<τ.im)
/-- The SAME whole original candidate is a surface in native algebraic
Krull dimension. Genuine nine-chart covering handles EVERY scheme prime. -/
lemma dimension : topologicalKrullDim (candidate τ hτ)=2 := by
  apply le_antisymm
  · let Y (j : Label 3) : Type := Spec (CommRingCat.of (CoordinateChart τ hτ j))
    refine SoberOpenCoverDimension318.dimension_le Y
      (fun j => chartMap τ hτ j) (fun j => (chartMap τ hτ j).isOpenEmbedding) ?_ 2 ?_
    · intro x
      exact ⟨(cover τ hτ).idx x,(cover τ hτ).covers x⟩
    · intro j
      exact (PELOriginalChartKrullDimension318.spec_dimension τ hτ j).le
  · let j : Label 3 := (0,0)
    calc
      2=topologicalKrullDim (Spec (CommRingCat.of (CoordinateChart τ hτ j))) :=
        (PELOriginalChartKrullDimension318.spec_dimension τ hτ j).symm
      _≤topologicalKrullDim (candidate τ hτ) :=
        (chartMap τ hτ j).isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- Existing proper/smooth/integral group geometry and the NEW actual
algebraic surface dimension refer to exactly the same scheme and base. -/
lemma geometric_surface :
    IsProper (PELOriginalProductChartCover318.π τ hτ) ∧
    Smooth (PELOriginalProductChartCover318.π τ hτ) ∧
    IsIntegral (candidate τ hτ) ∧ ConnectedSpace (candidate τ hτ) ∧
    topologicalKrullDim (candidate τ hτ)=2 := by
  obtain ⟨hp,hs,hi,hc⟩ := PELOriginalProperSmoothGroup318.geometric_properties τ hτ
  exact ⟨hp,hs,hi,hc,dimension τ hτ⟩
end PELOriginalCandidateAlgebraicDimension318
