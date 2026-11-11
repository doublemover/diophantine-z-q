module
public import InjectivePrincipalField318
public import PELOriginalSexticSectionField318
public section
noncomputable section
namespace PELOriginalChartOverlapLocalization318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 PELOriginalChartSectionField318
open PELOriginalRatioEvaluationExt318 PELOriginalCubicRelationIdeal318
open PELOriginalGradedSectionRing318 HomogeneousQuotientChart318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)

abbrev Overlap := Localization.Away (ratioElement τ hτ j k)

lemma ratio_field_nonzero : embedding τ hτ j (ratioElement τ hτ j k) ≠ 0 := by
  rw [ratioElement,fraction_image]
  simp only [pow_one,variable_image]
  apply div_ne_zero
  · simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ k
  · simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ j

@[expose] def intoField : Overlap τ hτ j k →+* SectionField τ hτ :=
  InjectivePrincipalField318.toField (embedding τ hτ j)
    (ratioElement τ hτ j k) (ratio_field_nonzero τ hτ j k)

lemma intoField_injective : Function.Injective (intoField τ hτ j k) :=
  InjectivePrincipalField318.injective (embedding τ hτ j) (embedding_injective τ hτ j)
    (ratioElement τ hτ j k) (ratio_field_nonzero τ hτ j k)

lemma intoField_coefficient (a : CoordinateChart τ hτ j) :
    intoField τ hτ j k (algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k) a)=
      embedding τ hτ j a := InjectivePrincipalField318.coefficient _ _ _ _

lemma intoField_scalar (c : ℂ) :
    intoField τ hτ j k (algebraMap ℂ (Overlap τ hτ j k) c)=algebraMap ℂ (SectionField τ hτ) c := by
  rw [IsScalarTower.algebraMap_apply ℂ (CoordinateChart τ hτ j) (Overlap τ hτ j k),
    intoField_coefficient,embedding_scalar]

@[expose] def chartRatios (i : Label 3) : Overlap τ hτ j k :=
  algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k) (ratioElement τ hτ j i) *
    IsLocalization.Away.invSelf (ratioElement τ hτ j k)

lemma chartRatios_field (i : Label 3) :
    intoField τ hτ j k (chartRatios τ hτ j k i)=embedding τ hτ k (ratioElement τ hτ k i) := by
  rw [chartRatios,map_mul,intoField_coefficient]
  rw [show intoField τ hτ j k (IsLocalization.Away.invSelf (ratioElement τ hτ j k))=
    (embedding τ hτ j (ratioElement τ hτ j k))⁻¹ from
      InjectivePrincipalField318.inverse _ _ _]
  simp only [ratioElement,fraction_image,pow_one,variable_image]
  have hj : algebraMap (Ring τ hτ) (SectionField τ hτ) (generators τ hτ j) ≠ 0 := by
    simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ j
  have hk : algebraMap (Ring τ hτ) (SectionField τ hτ) (generators τ hτ k) ≠ 0 := by
    simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ k
  field_simp [hj,hk]

lemma polynomial_field (p : Equations) :
    intoField τ hτ j k (MvPolynomial.aeval (chartRatios τ hτ j k) p)=
      embedding τ hτ k (MvPolynomial.aeval (ratioElement τ hτ k) p) := by
  change intoField τ hτ j k (p.eval₂ _ _) = embedding τ hτ k (p.eval₂ _ _)
  rw [MvPolynomial.hom_eval₂,MvPolynomial.hom_eval₂]
  congr 1
  · ext c
    exact (intoField_scalar τ hτ j k c).trans (embedding_scalar τ hτ k c).symm
  · funext i
    exact chartRatios_field τ hτ j k i

lemma relations_killed :
    RingHom.ker (MvPolynomial.aeval (ratioElement τ hτ k)).toRingHom ≤
      RingHom.ker (MvPolynomial.aeval (chartRatios τ hτ j k)).toRingHom := by
  intro p hp
  change MvPolynomial.aeval (ratioElement τ hτ k) p=0 at hp
  change MvPolynomial.aeval (chartRatios τ hτ j k) p=0
  apply intoField_injective τ hτ j k
  rw [polynomial_field,hp,map_zero,map_zero]

/-- The actual opposite WHOLE chart maps into the literal principal
localization at cubic_k/cubic_j. All relations, not only generators,
are retained by the full ratio presentation and faithful field square. -/
@[expose] def fromOther : CoordinateChart τ hτ k →ₐ[ℂ] Overlap τ hτ j k :=
  AlgHom.liftOfSurjective (MvPolynomial.aeval (ratioElement τ hτ k))
    (polynomial_surjective τ hτ k) (MvPolynomial.aeval (chartRatios τ hτ j k))
    (relations_killed τ hτ j k)

lemma fromOther_field (a : CoordinateChart τ hτ k) :
    intoField τ hτ j k (fromOther τ hτ j k a)=embedding τ hτ k a := by
  obtain ⟨p,rfl⟩ := polynomial_surjective τ hτ k a
  rw [fromOther,AlgHom.liftOfSurjective_apply,polynomial_field]

lemma fromOther_ratio (i : Label 3) :
    fromOther τ hτ j k (ratioElement τ hτ k i)=chartRatios τ hτ j k i := by
  apply intoField_injective τ hτ j k
  rw [fromOther_field,chartRatios_field]

/-- Genuine equality in the actual overlap R_j[(c_k/c_j)⁻¹],
with its exact quadratic transition unit. -/
theorem sextic_transition (s : PELOriginalSectionMultiplication318.homogeneous τ hτ 6) :
    algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k)
      (PELOriginalSexticRegularization318.linear τ hτ j s)=
    fromOther τ hτ j k (PELOriginalSexticRegularization318.linear τ hτ k s) *
      (algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k) (ratioElement τ hτ j k))^2 := by
  apply intoField_injective τ hτ j k
  rw [map_mul,map_pow,intoField_coefficient,intoField_coefficient,fromOther_field]
  exact PELOriginalSexticSectionField318.transition τ hτ j k s
end PELOriginalChartOverlapLocalization318
