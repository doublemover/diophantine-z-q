module
public import PELOriginalMixedPointEvaluation318
public section
noncomputable section
namespace PELOriginalMixedPowerUnit318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalChartAnalyticEvaluation318 PELOriginalCandidateComplexPoints318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalMixedPointEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

/-- A genuine whole mixed-chart regular function, obtained from the
already constructed full H0(6) regularization. Its value is theta2_s³ /
cubic_j², so it compares degree TWO cubed with degree THREE squared. -/
@[expose] def value (a : Index) : Γ((mixedOpen τ hτ a).toScheme,⊤) :=
  (toAffine τ hτ a).appTop ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ a.1))).inv
    (PELOriginalLevelTwoCubicProducts318.denominator τ hτ a.1 a.2))

lemma evaluation (a : Index)
    (p : Spec (CommRingCat.of ℂ) ⟶ (mixedOpen τ hτ a).toScheme)
    (z : ComplexVectors) (h3 : PELOriginalLevelPowerSections318.value τ hτ 3 a.1 z≠0)
    (he : p ≫ (mixedOpen τ hτ a).ι = candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (value τ hτ a)) =
      (PELOriginalLevelPowerSections318.value τ hτ 2 a.2 z)^3 /
        (PELOriginalLevelPowerSections318.value τ hτ 3 a.1 z)^2 := by
  have hA : p ≫ toAffine τ hτ a =
      Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z a.1 h3).toRingHom) := by
    apply (cancel_mono (chartMap τ hτ a.1)).1
    rw [Category.assoc,toAffine_chart,he,PELOriginalChartSchemePointIdentity318.chart_point]
  rw [value,element_evaluation τ hτ a _ p z h3 hA,
    PELOriginalLevelTwoCubicProducts318.denominator_evaluation]

/-- The section is an ACTUAL global regular unit on the whole mixed
scheme open. Invertibility at all primes follows from the genuine
complex point unit criterion, not a pointwise analytic inverse. -/
theorem isUnit (a : Index) : IsUnit (value τ hτ a) := by
  let π := (mixedOpen τ hτ a).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : LocallyOfFiniteType π := by dsimp [π]; infer_instance
  apply ReducedSchemeGlobalFunctionSeparation318.isUnit π
  intro p hp
  obtain ⟨z,h3,h2,hA,he⟩ := point_representation τ hτ a p hp
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (value τ hτ a))) := by
    rw [evaluation τ hτ a p z h3 he]
    exact isUnit_iff_ne_zero.mpr (div_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 2 h3))
  simpa only [←ConcreteCategory.comp_apply,Iso.hom_inv_id,ConcreteCategory.id_apply] using
    hu.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv

@[expose] def unit (a : Index) : Γ((mixedOpen τ hτ a).toScheme,⊤)ˣ := (isUnit τ hτ a).unit
lemma unit_value (a : Index) : (unit τ hτ a).val=value τ hτ a := IsUnit.unit_spec _
end PELOriginalMixedPowerUnit318
