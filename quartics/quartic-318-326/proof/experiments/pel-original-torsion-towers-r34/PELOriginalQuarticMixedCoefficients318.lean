module
public import PELOriginalOpenFunctionSeparation318
public import PELOriginalMixedPowerUnit318
public import PELOriginalWholePowerGlobalSections318
public section
noncomputable section
namespace PELOriginalQuarticMixedCoefficients318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
open PELOriginalSectionMultiplication318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPowerSectionLift318 PELOriginalWholeHZeroDimension318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Pad EVERY original degree-four section by the actual quadratic
coordinate, producing an already algebraized full degree-six section. -/
@[expose] def padded (s : homogeneous τ hτ 4) (i : Label 2) : homogeneous τ hτ 6 :=
  multiply τ hτ 4 2 s (thetaVector τ hτ 2 i)
lemma padded_lift (s : homogeneous τ hτ 4) (i : Label 2) (z : ComplexVectors) :
    lift τ hτ 6 (asSection τ hτ 6 (padded τ hτ s i)) z=
      lift τ hτ 4 (asSection τ hτ 4 s) z*PELOriginalLevelPowerSections318.value τ hτ 2 i z := by
  simp only [padded,lift_product,theta_lift]

@[expose] def numerator (a : PELOriginalMixedRatioCover318.Index) (s : homogeneous τ hτ 4) :
    Γ((mixedOpen τ hτ a).toScheme,⊤) :=
  (toAffine τ hτ a).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (PELOriginalCandidateAffineCharts318.CoordinateChart τ hτ a.1))).inv
      (PELOriginalSexticRegularization318.linear τ hτ a.1 (padded τ hτ s a.2)))

/-- The division is by an independently proved GLOBAL REGULAR UNIT
on the entire mixed open, never by a pointwise analytic denominator. -/
@[expose] def regular (a : PELOriginalMixedRatioCover318.Index) (s : homogeneous τ hτ 4) :
    Γ((mixedOpen τ hτ a).toScheme,⊤) :=
  numerator τ hτ a s*((PELOriginalMixedPowerUnit318.unit τ hτ a)⁻¹).val

lemma regular_evaluation (a : PELOriginalMixedRatioCover318.Index) (s : homogeneous τ hτ 4)
    (p : Spec (CommRingCat.of ℂ) ⟶ (mixedOpen τ hτ a).toScheme)
    (z : ComplexVectors) (h3 : PELOriginalLevelPowerSections318.value τ hτ 3 a.1 z≠0)
    (h2 : PELOriginalLevelPowerSections318.value τ hτ 2 a.2 z≠0)
    (he : p≫(mixedOpen τ hτ a).ι=candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (regular τ hτ a s))=
      lift τ hτ 4 (asSection τ hτ 4 s) z/(PELOriginalLevelPowerSections318.value τ hτ 2 a.2 z)^2 := by
  have hA : p≫toAffine τ hτ a=Spec.map (CommRingCat.ofHom
      (PELOriginalChartAnalyticEvaluation318.algebraEvaluation τ hτ z a.1 h3).toRingHom) := by
    apply (cancel_mono (PELOriginalCandidateAffineCharts318.chartMap τ hτ a.1)).1
    rw [Category.assoc,toAffine_chart,he,PELOriginalChartSchemePointIdentity318.chart_point]
  have hn : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (numerator τ hτ a s))=
      lift τ hτ 4 (asSection τ hτ 4 s) z*PELOriginalLevelPowerSections318.value τ hτ 2 a.2 z /
        (PELOriginalLevelPowerSections318.value τ hτ 3 a.1 z)^2 := by
    rw [numerator,element_evaluation τ hτ a _ p z h3 hA,
      PELOriginalSexticRegularization318.cover_evaluation,PELOriginalSexticRatioCover318.coverRatio,padded_lift]
  let F := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp p.appTop.hom
  have hu : F ((PELOriginalMixedPowerUnit318.unit τ hτ a)⁻¹).val=
      (F (PELOriginalMixedPowerUnit318.value τ hτ a))⁻¹ := by
    change (Units.map F.toMonoidHom ((PELOriginalMixedPowerUnit318.unit τ hτ a)⁻¹)).val=_
    rw [map_inv,Units.val_inv_eq_inv_val,Units.coe_map,PELOriginalMixedPowerUnit318.unit_value]
  change F (numerator τ hτ a s*((PELOriginalMixedPowerUnit318.unit τ hτ a)⁻¹).val)=_
  rw [map_mul,hu]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (numerator τ hτ a s))*
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (PELOriginalMixedPowerUnit318.value τ hτ a)))⁻¹=_
  rw [hn,PELOriginalMixedPowerUnit318.evaluation τ hτ a p z h3 he]
  field_simp [h3,h2]

@[expose] def coefficient (a : NonemptyIndex τ hτ) (s : homogeneous τ hτ 4) :
    Γ(candidate τ hτ,opens τ hτ a) :=
  (LineFrameTopScalar318.ringTop (opens τ hτ a)).hom (regular τ hτ a.val s)

lemma coefficient_value (a : NonemptyIndex τ hτ) (s : homogeneous τ hτ 4) (z : ComplexVectors)
    (hz : z∈domain τ hτ (opens τ hτ a)) :
    PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ a) (coefficient τ hτ a s) z=
      lift τ hτ 4 (asSection τ hτ 4 s) z/(PELOriginalLevelPowerSections318.value τ hτ 2 a.val.2 z)^2 := by
  let p := point τ hτ (opens τ hτ a) z hz
  have he := point_ι τ hτ _ z hz
  have hn := coordinates_nonzero τ hτ a.val p z he
  rw [value_at_point τ hτ _ _ z p he]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop (opens τ hτ a)).inv (coefficient τ hτ a s)))=_
  rw [coefficient,Iso.hom_inv_id_apply]
  exact regular_evaluation τ hτ a.val s p z hn.1 hn.2 he
end PELOriginalQuarticMixedCoefficients318
