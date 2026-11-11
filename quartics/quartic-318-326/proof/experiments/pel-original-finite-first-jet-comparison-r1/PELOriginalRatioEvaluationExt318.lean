module
public import PELOriginalChartEvaluationRegularity318
public import PELOriginalProjectedChartIndependence318
public section
noncomputable section
namespace PELOriginalRatioEvaluationExt318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCubicRelationIdeal318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 PELOriginalChartSectionField318
open PELOriginalProjectedChartIndependence318 HomogeneousQuotientChart318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

lemma eval₂_scale {ι R K : Type*} [CommRing R] [CommRing K]
    (p : MvPolynomial ι R) (n : ℕ) (hp : p.IsHomogeneous n)
    (f : R →+* K) (c : K) (v : ι → K) :
    p.eval₂ f (fun i => c * v i) = c ^ n * p.eval₂ f v := by
  simpa only [MvPolynomial.eval₂_eq_eval_map] using
    HomogeneousEvaluationScaling318.evaluate_scale (MvPolynomial.map f p) n (hp.map f) c v

/-- Every homogeneous chart fraction is the SAME homogeneous polynomial
in the original ratios, as an equality in the WHOLE original chart ring. -/
theorem fraction_as_polynomial (n : ℕ) (p : Equations) (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval (ratioElement τ hτ j) p =
      (quotientMap (relations τ hτ) j).rangeRestrict (fraction j n p hp) := by
  apply embedding_injective τ hτ j
  let F := algebraMap (Ring τ hτ) (SectionField τ hτ)
  let v : Label 3 → SectionField τ hτ := fun i => F (generators τ hτ i)
  have hc : (embedding τ hτ j).comp (algebraMap ℂ (CoordinateChart τ hτ j)) =
      algebraMap ℂ (SectionField τ hτ) := by
    ext c
    exact embedding_scalar τ hτ j c
  have hv : (fun i => embedding τ hτ j (ratioElement τ hτ j i)) =
      (fun i => (v j)⁻¹ * v i) := by
    funext i
    rw [ratioElement,fraction_image]
    simp only [pow_one,variable_image]
    exact div_eq_inv_mul _ _
  have hF : F.comp (algebraMap ℂ (Ring τ hτ)) = algebraMap ℂ (SectionField τ hτ) := by
    ext c
    exact IsScalarTower.algebraMap_apply ℂ (Ring τ hτ) (SectionField τ hτ) c
  have he : p.eval₂ (algebraMap ℂ (SectionField τ hτ)) v = F (presentation τ hτ p) := by
    rw [←hF,←MvPolynomial.hom_eval₂]
    rfl
  change embedding τ hτ j (p.eval₂ (algebraMap ℂ (CoordinateChart τ hτ j))
    (ratioElement τ hτ j)) = _
  rw [MvPolynomial.hom_eval₂,hc,hv,eval₂_scale p n hp,he,fraction_image]
  simp only [F,v,inv_pow,div_eq_mul_inv,mul_comm]

/-- Full-ring generation, not only generation of the fraction field. -/
theorem polynomial_surjective : Function.Surjective (MvPolynomial.aeval (ratioElement τ hτ j)) := by
  intro a
  obtain ⟨n,p,hp,rfl⟩ := PELOriginalChartEvaluationRegularity318.exists_fraction τ hτ j a
  exact ⟨p,fraction_as_polynomial τ hτ j n p hp⟩

lemma ratio_self : ratioElement τ hτ j j = 1 := by
  apply embedding_injective τ hτ j
  rw [ratioElement,fraction_image,map_one]
  simp only [pow_one,variable_image]
  apply div_self
  simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ j

/-- Fixing scalars and ALL original ratios determines a ring map on the
entire affine chart, before any further principal localization. -/
theorem ringHom_ext_ratios {K : Type*} [CommRing K]
    (f g : CoordinateChart τ hτ j →+* K)
    (hc : ∀ c : ℂ, f (algebraMap ℂ _ c) = g (algebraMap ℂ _ c))
    (hr : ∀ i : Label 3, f (ratioElement τ hτ j i) = g (ratioElement τ hτ j i)) : f = g := by
  have hC : f.comp (algebraMap ℂ _) = g.comp (algebraMap ℂ _) := RingHom.ext hc
  ext a
  obtain ⟨p,rfl⟩ := polynomial_surjective τ hτ j a
  change f (p.eval₂ _ _) = g (p.eval₂ _ _)
  rw [MvPolynomial.hom_eval₂,MvPolynomial.hom_eval₂,hC]
  congr 1
  exact funext hr

/-- The same extensionality survives localization at ANY actual source
chart element. Inverse denominators are forced by the ring-map law. -/
theorem localized_ringHom_ext_ratios (a : CoordinateChart τ hτ j)
    {K : Type*} [CommRing K] (f g : Localization.Away a →+* K)
    (hc : ∀ c : ℂ, f (algebraMap _ (Localization.Away a) (algebraMap ℂ _ c)) =
      g (algebraMap _ (Localization.Away a) (algebraMap ℂ _ c)))
    (hr : ∀ i : Label 3, f (algebraMap _ (Localization.Away a) (ratioElement τ hτ j i)) =
      g (algebraMap _ (Localization.Away a) (ratioElement τ hτ j i))) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  exact ringHom_ext_ratios τ hτ j (f.comp (algebraMap _ _))
    (g.comp (algebraMap _ _)) hc hr
/-- The fixed target-coordinate indexing omits only the ratio X_j/X_j=1.
Thus agreement on exactly the original ratioVector coordinates suffices. -/
theorem localized_ringHom_ext_coordinates (a : CoordinateChart τ hτ j)
    {K : Type*} [CommRing K] (f g : Localization.Away a →+* K)
    (hc : ∀ c : ℂ, f (algebraMap _ (Localization.Away a) (algebraMap ℂ _ c)) =
      g (algebraMap _ (Localization.Away a) (algebraMap ℂ _ c)))
    (hr : ∀ i : TargetIndex,
      f (algebraMap _ (Localization.Away a) (coordinateElement τ hτ j i)) =
      g (algebraMap _ (Localization.Away a) (coordinateElement τ hτ j i))) : f = g := by
  classical
  apply localized_ringHom_ext_ratios τ hτ j a f g hc
  intro i
  by_cases hi : i = j
  · subst i
    simp only [ratio_self,map_one]
  · let k : TargetIndex := ComplexProjectiveComplexAtlas318.omittedEquiv (Label 3) 0 j ⟨i,hi⟩
    have hk : coordinateLabel j k = i := by
      exact congrArg Subtype.val ((ComplexProjectiveComplexAtlas318.omittedEquiv
        (Label 3) 0 j).symm_apply_apply ⟨i,hi⟩)
    simpa only [coordinateElement,hk] using hr k
end PELOriginalRatioEvaluationExt318
