module
public import PELOriginalFiniteOpenAnalyticMeeting318
public import ActualLocalizationCartesian318
public section
noncomputable section
namespace PELOriginalFiniteOpenBaseChange318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalProjectedFiniteOpen318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalChartSectionField318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The actual finite-open source is the WHOLE scheme preimage of the
literal polynomial base open under the original projected pair. -/
theorem cartesian (x : ComplexVectors) (p : BasePolynomial) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (CoordinateChart τ hτ j)
        (Localization.Away (polynomialMap τ hτ j x p)))))
      (localizedProjection τ hτ j x p)
      (Spec.map (CommRingCat.ofHom (polynomialMap τ hτ j x).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap BasePolynomial (Localization.Away p)))) :=
  ActualLocalizationCartesian318.square (polynomialMap τ hτ j x).toRingHom p

/-- Its embedding into the SAME integral proper candidate is a genuine
open immersion, not just an injection of original complex points. -/
theorem actual_open_immersion (x : ComplexVectors) (p : BasePolynomial) :
    IsOpenImmersion (localizedChart τ hτ j x p) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (CoordinateChart τ hτ j)
        (Localization.Away (polynomialMap τ hτ j x p))))) :=
    IsOpenImmersion.of_isLocalization (polynomialMap τ hτ j x p)
  change IsOpenImmersion (_ ≫ chartMap τ hτ j)
  infer_instance

/-- The exact complex scalar structure on every localized source is
the structure induced from the original candidate over Spec(C). -/
@[reassoc] theorem original_complex_base (x : ComplexVectors) (p : BasePolynomial) :
    localizedChart τ hτ j x p ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (Localization.Away (polynomialMap τ hτ j x p)))) := by
  rw [localizedChart,Category.assoc,PELOriginalCandidateChartBase318.chart_over_complex_base,
    ←Spec.map_comp]
  congr 1
  ext c
  exact (IsScalarTower.algebraMap_apply ℂ (CoordinateChart τ hτ j) _ c).symm

/-- The polynomial base map is over the original complex constants,
with the given two projected functions as its literal coordinates. -/
@[reassoc] theorem projection_over_complex_base (x : ComplexVectors) (p : BasePolynomial) :
    localizedProjection τ hτ j x p ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away p))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ
      (Localization.Away (polynomialMap τ hτ j x p)))) := by
  rw [localizedProjection,←Spec.map_comp]
  congr 1
  ext c
  rw [IsScalarTower.algebraMap_apply ℂ BasePolynomial (Localization.Away p)]
  simp only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq,AlgHom.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ (CoordinateChart τ hτ j) _ c).symm
end PELOriginalFiniteOpenBaseChange318
