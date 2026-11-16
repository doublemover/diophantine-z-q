module
public import PELOriginalUniversalHyperplaneInputs318
public import PELOriginalAllPowerMixedCoefficients318
public section
noncomputable section
namespace PELOriginalCubeBasisCoefficients318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalWholeHZeroDimension318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (4*N)]
structure Data where
  lineData : PELOriginalBalancedLineData318.Data τ hτ
  label : NonemptyIndex τ hτ → Label N
  gauge : ∀ i z,lineData.g i z=PELOriginalLevelPowerSections318.value τ hτ N (label i) z
  basis : ∀ i : NonemptyIndex τ hτ,Label (4*N) → Γ(candidate τ hτ,opens τ hτ i)
  basis_value : ∀ i r z,z∈domain τ hτ (opens τ hτ i) →
    PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ i) (basis i r) z=
      PELOriginalLevelPowerSections318.value τ hτ (4*N) r z/(lineData.g i z)^4

@[expose] def cubic : Data τ hτ 3 where
  lineData := PELOriginalBalancedHyperplaneSquares318.cubicData τ hτ
  label i := i.val.1
  gauge _ _ := rfl
  basis i r := PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ 4 i
    (thetaVector τ hτ 12 r)
  basis_value i r z hz := by
    let p := point τ hτ (opens τ hτ i) z hz
    have he := point_ι τ hτ _ z hz
    have hn := coordinates_nonzero τ hτ i.val p z he
    rw [value_at_point τ hτ _ _ z p he]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop (opens τ hτ i)).inv _))=_
    rw [PELOriginalWholePowerMixedTransition318.originalCoefficient,Iso.hom_inv_id_apply,
      PELOriginalWholePowerMixedCoefficient318.evaluation τ hτ 4 i.val _ p z hn.1 he]
    simp only [PELOriginalWholePowerRatioCover318.coverRatio,PELOriginalSexticRatioCover318.theta_lift]

/-- Same independently produced mixed power unit, in the literal open ring. -/
@[expose] def mixedUnit (i : NonemptyIndex τ hτ) : Γ(candidate τ hτ,opens τ hτ i)ˣ :=
  Units.map (LineFrameTopScalar318.ringTop (opens τ hτ i)).hom.hom.toMonoidHom
    (PELOriginalMixedPowerUnit318.unit τ hτ i.val)
lemma mixedUnit_value (i : NonemptyIndex τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (opens τ hτ i)) :
    PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ i) (mixedUnit τ hτ i).val z=
      (PELOriginalLevelPowerSections318.value τ hτ 2 i.val.2 z)^3/
        (PELOriginalLevelPowerSections318.value τ hτ 3 i.val.1 z)^2 := by
  let p := point τ hτ (opens τ hτ i) z hz
  have he := point_ι τ hτ _ z hz
  have hn := coordinates_nonzero τ hτ i.val p z he
  rw [value_at_point τ hτ _ _ z p he]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop (opens τ hτ i)).inv _))=_
  rw [mixedUnit,Units.coe_map,Iso.hom_inv_id_apply,PELOriginalMixedPowerUnit318.unit_value]
  exact PELOriginalMixedPowerUnit318.evaluation τ hτ i.val p z hn.1 he

/-- Actual H0(8) coefficients divided by the FOURTH power of a genuine
regular unit, giving theta8/theta2^4 on the whole mixed open. -/
@[expose] def quadratic : Data τ hτ 2 where
  lineData := PELOriginalBalancedHyperplaneSquares318.quadraticData τ hτ
  label i := i.val.2
  gauge _ _ := rfl
  basis i r := PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ 8 i
    (thetaVector τ hτ 8 r)*((mixedUnit τ hτ i)⁻¹).val^4
  basis_value i r z hz := by
    let ev := PELOriginalOpenRegularNaturality318.evaluation τ hτ (opens τ hτ i) z hz
    have hu : ev ((mixedUnit τ hτ i)⁻¹).val=(ev (mixedUnit τ hτ i).val)⁻¹ := by
      simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using congrArg Units.val
        (map_inv (Units.map ev.toMonoidHom) (mixedUnit τ hτ i))
    rw [value_eq_evaluation τ hτ _ _ z hz,map_mul,map_pow,hu]
    rw [←value_eq_evaluation τ hτ _ _ z hz,←value_eq_evaluation τ hτ _ _ z hz,
      PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ 8 i _ z hz,
      mixedUnit_value τ hτ i z hz]
    have hn := coordinates_nonzero τ hτ i.val (point τ hτ _ z hz) z (point_ι τ hτ _ z hz)
    simp only [PELOriginalSexticRatioCover318.theta_lift,PELOriginalTranslationFrameValues318.chartGauge,
      PELOriginalMixedTranslationGauge318.gauge]
    field_simp [hn.1,hn.2]
end PELOriginalCubeBasisCoefficients318
