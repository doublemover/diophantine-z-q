module
public import VaryingNormalizedFamilyPresentation318
public import VaryingWordGlobalFiniteFlat318
public section
noncomputable section
namespace VaryingGlobalFamilyPresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι
/-- The actual global universal family is finitely presented locally on
its whole parameter base, by its proved Cartesian word-chart squares. -/
instance presentation : LocallyOfFinitePresentation π := by
  apply IsZariskiLocalAtTarget.of_openCover (P:=@LocallyOfFinitePresentation)
    (VaryingWordChartGluing318.cover R A ι)
  intro w
  change LocallyOfFinitePresentation
    (pullback.snd π (VaryingWordChartGluing318.into R A ι w))
  rw [← (VaryingWordGlobalFamilyCartesian318.square R A ι w).isoPullback_inv_snd]
  infer_instance
end VaryingGlobalFamilyPresentation318
