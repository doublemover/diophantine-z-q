module
public import ChartGeneratedImageSheaf318
public import PELOriginalChartOverlapLocalization318
public import PELOriginalCandidateNineChartCover318
public section
noncomputable section
namespace PELOriginalAlgebraicHyperplaneImage318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalReducedProjectiveCandidate318
open PELOriginalCandidateAffineCharts318 PELOriginalRatioEvaluationExt318
open PELOriginalCandidateNineChartCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The actual nine cubic coordinate ratios, as genuine regular sections
on the independently constructed candidate's actual affine chart. -/
@[expose] def ratios (i : Label 3) :
    Γ(Spec (CommRingCat.of (CoordinateChart τ hτ j)),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).inv
    (ratioElement τ hτ j i)

lemma ratios_self : ratios τ hτ j j = 1 := by
  rw [ratios,ratio_self,map_one]

/-- A globally defined algebraic module sheaf on the SAME candidate:
the image of its nine literal cubic ratios in the direct image of the
chosen chart's structure sheaf. No analytic bundle is used to define it.
Full local frames on every other chart remain a separate theorem. -/
@[expose] def imageSheaf : (candidate τ hτ).Modules :=
  ChartGeneratedImageSheaf318.sheaf (chartMap τ hτ j) (ratios τ hτ j)

/-- Produced trivialization on the actual anchor chart. Its generator
is the literal j-th cubic ratio, which equals one in the whole ring. -/
@[expose] def anchorFrame :
    SheafOfModules.unit (Spec (CommRingCat.of (CoordinateChart τ hτ j))).ringCatSheaf ≅
      (Scheme.Modules.restrictFunctor (chartMap τ hτ j)).obj (imageSheaf τ hτ j) :=
  ChartGeneratedImageSheaf318.anchorFrame (chartMap τ hτ j) (ratios τ hτ j) j
    (ratios_self τ hτ j)
end PELOriginalAlgebraicHyperplaneImage318
