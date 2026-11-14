module
public import PELOriginalSeparatingDerivativeNonzero318
public import PELOriginalFullCandidateSchemePoints318
public section
noncomputable section
namespace PELOriginalEveryPointSmoothNeighborhood318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidateNineChartCover318 PELOriginalChartPrimitiveSeparator318
open PELOriginalDerivativeOpenCharts318 PELOriginalReducedProjectiveCandidate318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- EVERY original point lies in a genuine algebraic smooth principal
open of the SAME candidate. Its actual defining derivative is proved
nonzero at that specified point, with no denominator, genericity or
smoothness assumption left over. -/
theorem original_point (j : Label 3) (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : CoordinateChart τ hτ j,
      algebraEvaluation τ hτ x j hx d ≠ 0 ∧
      IsOpenImmersion (inclusion τ hτ j d) ∧
      Smooth (inclusion τ hτ j d ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ) ∧
      ∃ u : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away d)),
        u ≫ inclusion τ hτ j d =
          Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ x j hx).toRingHom) ≫
            chartMap τ hτ j := by
  obtain ⟨g,hf,hg,hd,e,he,hxe,hi⟩ :=
    PELOriginalFiniteUnramifiedProjection318.exists_finite_faithful_identity_chart τ hτ j x hx
  let f := algebraEvaluation τ hτ x j hx
  obtain ⟨c,hsep,hopen,hsmooth,hlift⟩ :=
    PELOriginalNormalizationSmoothNeighborhood318.exists_fiber_smooth_neighborhoods τ hτ j
      g hg hf (f.comp g)
  let t := weightedRatioElement τ hτ j c
  let d := PELOriginalNormalizationSmoothNeighborhood318.derivativeElement τ hτ j g t
  have hnonzero : f d ≠ 0 :=
    PELOriginalSeparatingDerivativeNonzero318.derivative_nonzero τ hτ j g hg hf x hx e he hxe t hsep
  exact ⟨d,hnonzero,hopen,hsmooth,hlift f hnonzero⟩

/-- Every ACTUAL over-C morphism from Spec(C) into the entire candidate
factors through one of these algebraic smooth opens. This uses the full
scheme-point realization, including all old denominator boundaries. -/
theorem every_complex_point
    (p : Spec (CommRingCat.of ℂ) ⟶ candidate τ hτ)
    (hp : p ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _) :
    ∃ j : Label 3, ∃ d : CoordinateChart τ hτ j,
      IsOpenImmersion (inclusion τ hτ j d) ∧
      Smooth (inclusion τ hτ j d ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ) ∧
      ∃ u : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away d)),
        u ≫ inclusion τ hτ j d = p := by
  obtain ⟨j,x,hx,hp'⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ p hp
  obtain ⟨d,hd,ho,hs,u,hu⟩ := original_point τ hτ j x hx
  exact ⟨j,d,ho,hs,u,hu.trans hp'.symm⟩
end PELOriginalEveryPointSmoothNeighborhood318
