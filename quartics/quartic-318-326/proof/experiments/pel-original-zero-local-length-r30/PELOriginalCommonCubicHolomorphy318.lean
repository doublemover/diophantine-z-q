module
public import PELOriginalCommonCubicFibers318
public import PELOriginalRegularCoordinateHolomorphy318
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public section
noncomputable section
namespace PELOriginalCommonCubicHolomorphy318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalRegularCoverPatches318
open PELOriginalGluedLegendreMap318 PELOriginalManuscriptNormalization318
open PELOriginalCommonCubicCoordinate318 PELOriginalOrderedMatrixTransport318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i

/-- Holomorphy in the ACTUAL original atlas at every point over the
finite common manuscript base, away from the original branch locus.
Finiteness is necessary: the old regular locus can contain a new pole. -/
theorem ordinate_holomorphic (x:CharacterBase i) (hx:x∈Regular i)
    (t:ℂ) (ht:coordinate (toMaximal i x)=(t:OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (PELOriginalCommonCubicCoordinate318.ordinate i) x := by
  have hc:=PELOriginalRegularCoordinateHolomorphy318.coordinates_holomorphic i x hx
  have hd:=((matrixChange i).finite_value _ _ (actual_ordered_image i x hx t ht)).1
  let F:ℂ×ℂ→ℂ:=fun v=>scale i*(ordinateScale i*v.2/
    ((matrixChange i).c*v.1+(matrixChange i).d)^2)
  have hF:AnalyticAt ℂ F (coordinates i x):=by
    exact analyticAt_const.mul ((analyticAt_const.mul analyticAt_snd).div
      (((analyticAt_const.mul analyticAt_fst).add analyticAt_const).pow 2)
      (pow_ne_zero 2 hd))
  have hm:ContMDiffAt 𝓘(ℂ,ℂ×ℂ) 𝓘(ℂ,ℂ) ω F (coordinates i x):=
    contMDiffAt_iff_contDiffAt.mpr hF.contDiffAt
  exact hm.comp x (hc.1.prodMk_space hc.2)
end PELOriginalCommonCubicHolomorphy318
