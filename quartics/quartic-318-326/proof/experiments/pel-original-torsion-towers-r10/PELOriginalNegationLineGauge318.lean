module
public import PELOriginalNegationLineCover318
public import PELOriginalLevelThetaNegation318
public section
noncomputable section
namespace PELOriginalNegationLineGauge318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
open PELOriginalNegationLineCover318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Both symmetry coefficients are already genuine regular functions,
obtained from actual cubic/quadratic projective ratios. -/
@[expose] def cubicValue (a : Index τ hτ) : Γ((chart τ hτ a).toScheme,⊤) :=
  ((candidate τ hτ).homOfLE (show chart τ hτ a ≤ opens τ hτ a.1 from inf_le_left)).appTop
    (cubic τ hτ a.1.val (-a.2.val.1))
@[expose] def quadraticValue (a : Index τ hτ) : Γ((chart τ hτ a).toScheme,⊤) :=
  ((candidate τ hτ).homOfLE (show chart τ hτ a ≤ opens τ hτ a.1 from inf_le_left)).appTop
    (quadratic τ hτ a.1.val (-a.2.val.2))

lemma evaluations (a : Index τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (chart τ hτ a))
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a).toScheme)
    (hp : p≫(chart τ hτ a).ι=candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (cubicValue τ hτ a))=
      PELOriginalLevelPowerSections318.value τ hτ 3 a.2.val.1 (-z)/
        PELOriginalLevelPowerSections318.value τ hτ 3 a.1.val.1 z ∧
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (quadraticValue τ hτ a))=
      PELOriginalLevelPowerSections318.value τ hτ 2 a.2.val.2 (-z)/
        PELOriginalLevelPowerSections318.value τ hτ 2 a.1.val.2 z := by
  let q := p≫(candidate τ hτ).homOfLE
    (show chart τ hτ a ≤ opens τ hτ a.1 from inf_le_left)
  have hq : q≫(opens τ hτ a.1).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [q,Category.assoc,Scheme.homOfLE_ι] using hp
  have hqC : q≫(opens τ hτ a.1).ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _ := by
    rw [←Category.assoc,hq,PELOriginalProperComplexCandidate318.candidate_point_over]
  have hn := PELOriginalTranslationFrameValues318.theta_nonzero τ hτ a.1 z
    ((domain_iff τ hτ a z).mp hz).1
  constructor
  · change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (q.appTop (cubic τ hτ a.1.val (-a.2.val.1)))=_
    rw [cubic_evaluation τ hτ a.1.val (-a.2.val.1) q hqC z hn.1 hq,
      PELOriginalLevelThetaNegation318.value_neg]
  · change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (q.appTop (quadratic τ hτ a.1.val (-a.2.val.2)))=_
    rw [quadratic_evaluation τ hτ a.1.val (-a.2.val.2) q hqC z hn.2 hq,
      PELOriginalLevelThetaNegation318.value_neg]

/-- Nonvanishing at actual complex points is upgraded to a REGULAR
unit on the WHOLE scheme open, including every nonclosed prime. -/
lemma units (a : Index τ hτ) : IsUnit (cubicValue τ hτ a) ∧ IsUnit (quadraticValue τ hτ a) := by
  let π := (chart τ hτ a).ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : LocallyOfFiniteType π := by dsimp [π]; infer_instance
  have hvalues (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a).toScheme) (hp : p≫π=𝟙 _) :
      IsUnit (p.appTop (cubicValue τ hτ a)) ∧ IsUnit (p.appTop (quadraticValue τ hτ a)) := by
    obtain ⟨z,hz,he⟩ := point_representation τ hτ a p hp
    have hs := PELOriginalTranslationFrameValues318.theta_nonzero τ hτ a.1 z
      ((domain_iff τ hτ a z).mp hz).1
    have ht := PELOriginalTranslationFrameValues318.theta_nonzero τ hτ a.2 (-z)
      ((domain_iff τ hτ a z).mp hz).2
    have hc := evaluations τ hτ a z hz p he
    have h3 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (cubicValue τ hτ a))) := by
      rw [hc.1]
      exact isUnit_iff_ne_zero.mpr (div_ne_zero ht.1 hs.1)
    have h2 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (quadraticValue τ hτ a))) := by
      rw [hc.2]
      exact isUnit_iff_ne_zero.mpr (div_ne_zero ht.2 hs.2)
    constructor
    · simpa only [←ConcreteCategory.comp_apply,Iso.hom_inv_id,ConcreteCategory.id_apply] using
        h3.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
    · simpa only [←ConcreteCategory.comp_apply,Iso.hom_inv_id,ConcreteCategory.id_apply] using
        h2.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
  exact ⟨ReducedSchemeGlobalFunctionSeparation318.isUnit π _ (fun p hp => (hvalues p hp).1),
    ReducedSchemeGlobalFunctionSeparation318.isUnit π _ (fun p hp => (hvalues p hp).2)⟩

/-- The actual symmetry gauge: target cubic/quadratic gauge divided by
source cubic/quadratic gauge, as a unit of the ORIGINAL structure sheaf. -/
@[expose] def gauge (a : Index τ hτ) : Γ(candidate τ hτ,chart τ hτ a)ˣ :=
  Units.map (LineFrameTopScalar318.ringTop (chart τ hτ a)).hom.hom.toMonoidHom
    ((units τ hτ a).1.unit*((units τ hτ a).2.unit)⁻¹)

lemma gauge_value (a : Index τ hτ) (z : ComplexVectors) (hz : z∈domain τ hτ (chart τ hτ a)) :
    PELOriginalOpenRegularFunction318.value τ hτ (chart τ hτ a) (gauge τ hτ a).val z=
      PELOriginalTranslationFrameValues318.chartGauge τ hτ a.2 (-z)/
        PELOriginalTranslationFrameValues318.chartGauge τ hτ a.1 z := by
  let p := point τ hτ (chart τ hτ a) z hz
  have he := evaluations τ hτ a z hz p (point_ι τ hτ _ z hz)
  rw [value_at_point τ hτ _ _ z p (point_ι τ hτ _ z hz)]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop (chart τ hτ a)).inv (gauge τ hτ a).val))=_
  simp only [gauge,Units.coe_map,Iso.hom_inv_id_apply]
  let F := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp p.appTop.hom
  change (Units.map F.toMonoidHom
    ((units τ hτ a).1.unit*((units τ hτ a).2.unit)⁻¹)).val=_
  simp only [map_mul,map_inv,Units.val_mul,Units.val_inv_eq_inv_val,Units.coe_map,IsUnit.unit_spec]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (cubicValue τ hτ a)) *
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (quadraticValue τ hτ a)))⁻¹=_
  rw [he.1,he.2]
  dsimp only [PELOriginalTranslationFrameValues318.chartGauge,PELOriginalMixedTranslationGauge318.gauge]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring
end PELOriginalNegationLineGauge318
