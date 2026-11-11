module
public import PELOriginalQuarticGlobalRecovery318
public import PELOriginalWholePowerRegularization318
public import PELOriginalTranslationFrameValues318
public section
noncomputable section
namespace PELOriginalAllPowerMixedCoefficients318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
open PELOriginalSectionMultiplication318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPowerSectionLift318 PELOriginalWholeHZeroDimension318
open PELOriginalPowerSectionDescent318 PELOriginalPolarizationAutomorphy318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalTranslationFrameValues318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ)

/-- Pad an ARBITRARY original H0(n) by the nth power of a quadratic
coordinate. Its literal original multiplier has degree n+2n=3n. -/
@[expose] def paddedAutomorphic (s : homogeneous τ hτ n) (i : Label 2) :
    OriginalAutomorphic τ hτ (3*n) where
  value z := lift τ hτ n (asSection τ hτ n s) z*(PELOriginalLevelPowerSections318.value τ hτ 2 i z)^n
  entire := (PELOriginalPowerSectionLift318.entire τ hτ n _).mul
    ((PELOriginalLevelPowerSections318.holomorphic τ hτ 2 i).pow n)
  lattice_rule l z := by
    rw [PELOriginalPowerSectionLift318.original_automorphy,
      PELOriginalLevelPowerSections318.original_automorphy,mul_pow,←pow_mul]
    have hd : 3*n=n+2*n := by omega
    rw [hd,pow_add]
    ring
@[expose] def padded (s : homogeneous τ hτ n) (i : Label 2) : homogeneous τ hτ (3*n) :=
  ⟨(descend τ hτ (3*n) (paddedAutomorphic τ hτ n s i)).value,
    (descend τ hτ (3*n) (paddedAutomorphic τ hτ n s i)).holomorphic⟩
lemma padded_lift (s : homogeneous τ hτ n) (i : Label 2) (z : ComplexVectors) :
    lift τ hτ (3*n) (asSection τ hτ (3*n) (padded τ hτ n s i)) z=
      lift τ hτ n (asSection τ hτ n s) z*(PELOriginalLevelPowerSections318.value τ hτ 2 i z)^n :=
  lift_descend τ hτ (3*n) (paddedAutomorphic τ hτ n s i) z

/-- No analytic division is used: the numerator itself has degree3n,
so whole cubic regularization already gives the actual degree-n coefficient. -/
@[expose] def regular (a : PELOriginalMixedRatioCover318.Index) (s : homogeneous τ hτ n) :
    Γ((mixedOpen τ hτ a).toScheme,⊤) :=
  (toAffine τ hτ a).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (PELOriginalCandidateAffineCharts318.CoordinateChart τ hτ a.1))).inv
      (PELOriginalWholePowerRegularization318.linear τ hτ n a.1 (padded τ hτ n s a.2)))
@[expose] def coefficient (a : NonemptyIndex τ hτ) (s : homogeneous τ hτ n) :
    Γ(candidate τ hτ,opens τ hτ a) :=
  (LineFrameTopScalar318.ringTop (opens τ hτ a)).hom (regular τ hτ n a.val s)

lemma coefficient_value (a : NonemptyIndex τ hτ) (s : homogeneous τ hτ n) (z : ComplexVectors)
    (hz : z∈chartDomain τ hτ a) :
    PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ a) (coefficient τ hτ n a s) z=
      lift τ hτ n (asSection τ hτ n s) z/(chartGauge τ hτ a z)^n := by
  let p := point τ hτ (opens τ hτ a) z hz
  have he := point_ι τ hτ _ z hz
  have hn := coordinates_nonzero τ hτ a.val p z he
  have hA : p≫toAffine τ hτ a.val=Spec.map (CommRingCat.ofHom
      (PELOriginalChartAnalyticEvaluation318.algebraEvaluation τ hτ z a.val.1 hn.1).toRingHom) := by
    apply (cancel_mono (PELOriginalCandidateAffineCharts318.chartMap τ hτ a.val.1)).1
    rw [Category.assoc,toAffine_chart,he,PELOriginalChartSchemePointIdentity318.chart_point]
  rw [value_at_point τ hτ _ _ z p he]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop (opens τ hτ a)).inv (coefficient τ hτ n a s)))=_
  rw [coefficient,Iso.hom_inv_id_apply,regular,element_evaluation τ hτ a.val _ p z hn.1 hA,
    PELOriginalWholePowerRegularization318.cover_evaluation]
  change lift τ hτ (3*n) (asSection τ hτ (3*n) (padded τ hτ n s a.val.2)) z /
    (PELOriginalLevelPowerSections318.value τ hτ 3 a.val.1 z)^n=_
  rw [padded_lift]
  dsimp only [chartGauge,PELOriginalMixedTranslationGauge318.gauge]
  rw [div_pow,div_div_eq_mul_div]

lemma coefficient_add (a : NonemptyIndex τ hτ) (s t : homogeneous τ hτ n) :
    coefficient τ hτ n a (s+t)=coefficient τ hτ n a s+coefficient τ hτ n a t := by
  apply PELOriginalOpenFunctionSeparation318.ext τ hτ (opens τ hτ a)
  intro z hz
  rw [value_eq_evaluation τ hτ _ (_+_) z hz,map_add,
    ←value_eq_evaluation τ hτ _ _ z hz,←value_eq_evaluation τ hτ _ _ z hz,
    coefficient_value τ hτ n a (s+t) z hz,coefficient_value τ hτ n a s z hz,
    coefficient_value τ hτ n a t z hz]
  simp only [lift,asSection,Submodule.coe_add,Pi.add_apply,mul_add,add_div]
end PELOriginalAllPowerMixedCoefficients318
