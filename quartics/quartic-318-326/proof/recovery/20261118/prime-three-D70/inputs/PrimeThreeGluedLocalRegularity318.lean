module
public import PrimeThreeSecondChartRegularity318
public import PrimeThreeGluedIdealChartInvertibility318
public import Mathlib.AlgebraicGeometry.Noetherian
public section
noncomputable section
namespace PrimeThreeGluedLocalRegularity318
open AlgebraicGeometry CategoryTheory
open PrimeThreeGluedSecondModification318 PrimeThreeGluedIdealChartInvertibility318
attribute [local instance] OriginalPrimeThreeFirstURatioChart318.chartAlgebra
attribute [local instance] OriginalPrimeThreeFirstULocalBaseChange318.pointBaseAlgebra
attribute [local instance] OriginalPrimeThreeFirstULocalBaseChange318.chartRightAlgebra
attribute [local instance] PrimeThreeSecondChartRatios318.chartAlgebra
attribute [local instance] ReesHomogeneousRatioEquiv318.homogeneousBaseAlgebra

/-- The literal five coordinate rings of the existing whole-model cover. -/
theorem chart_regular (i : Fin 3 ⊕ Fin 2) : IsRegularRing (chartRing i) := by
  cases i with
  | inl i => exact PrimeThreeSecondChartRegularity318.second_chart_regular i
  | inr j =>
    letI : IsRegularRing
        (OriginalPrimeThreeSelectedFirstChartBaseChange318.LocalChart j.succ) :=
      PrimeThreeFirstChartRegularity318.unchanged_chart_regular j
    exact IsRegularRing.of_ringEquiv
      (OriginalPrimeThreeSelectedFirstChartAtlas318.actualSelectedChartEquiv j.succ).symm.toRingEquiv

/-- Finite affine cover Noetherianity is derived for the constructed
selected-PointRing scheme, rather than inferred from stalkwise statements. -/
theorem model_noetherian : IsNoetherian gluedSecondModification := by
  apply (isNoetherian_iff_of_finite_affine_openCover
    (𝒰 := affineCover.openCover)).mpr
  intro i
  letI : IsRegularRing (chartRing i) := chart_regular i
  change IsNoetherianRing Γ(Spec (chartRing i), ⊤)
  exact isNoetherianRing_of_ringEquiv (chartRing i)
    (Scheme.ΓSpecIso (chartRing i)).symm.commRingCatIsoToRingEquiv

/-- ALL actual scheme stalks of the glued modification over the selected
PointRing are regular local rings. Both affine and open-immersion stalk
maps are transported in their actual directions. This is not a theorem
about the entire arithmetic model, other bad primes, or other twists. -/
theorem all_stalks_regular (x : gluedSecondModification) :
    IsRegularLocalRing (gluedSecondModification.presheaf.stalk x) := by
  obtain ⟨i, y, hy⟩ := charts_cover x
  rw [← hy]
  letI : IsRegularRing (chartRing i) := chart_regular i
  letI : IsRegularLocalRing ((Spec (chartRing i)).presheaf.stalk y) :=
    IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (chartRing i) y).symm.commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((inclusion i).stalkMap y)).symm.commRingCatIsoToRingEquiv

end PrimeThreeGluedLocalRegularity318
