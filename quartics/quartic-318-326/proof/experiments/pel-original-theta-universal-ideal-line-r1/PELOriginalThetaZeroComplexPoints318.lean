module
public import PELOriginalThetaZeroScheme318
public import PrincipalZeroComplexPoints318
public import PELOriginalFullCandidateSchemePoints318
public section
noncomputable section
namespace PELOriginalThetaZeroComplexPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalOpenRegularFunction318
open PELOriginalTranslationFrameValues318 PELOriginalThetaZeroScheme318
open PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma local_value (a : NonemptyIndex τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (opens τ hτ a)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((point τ hτ (opens τ hτ a) z hz).appTop (localEquation τ hτ a))=
      PELOriginalLevelPowerSections318.value τ hτ 1 (0 : Label 1) z/chartGauge τ hτ a z := by
  change OpenPointScalarPullback318.value (opens τ hτ a) (coefficient τ hτ a)
    (point τ hτ (opens τ hτ a) z hz)=_
  rw [←value_at_point τ hτ _ _ z _ (point_ι τ hτ _ z hz),
    coefficient,PELOriginalAllPowerMixedCoefficients318.coefficient_value]
  simp only [PELOriginalSexticRatioCover318.theta_lift,pow_one]

/-- Exact underlying support at every original complex point, including
all old boundary points. The scheme itself still retains its full ideal. -/
theorem support_iff (z : ComplexVectors) :
    candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ) ∈
      Set.range (PELOriginalThetaZeroScheme318.inclusion τ hτ) ↔
        PELOriginalLevelPowerSections318.value τ hτ 1 (0 : Label 1) z=0 := by
  obtain ⟨a,ha⟩ := chart_cover τ hτ z
  let p := point τ hτ (opens τ hτ a) z ha
  have hp := point_ι τ hτ (opens τ hτ a) z ha
  have hlocal : p (IsLocalRing.closedPoint ℂ) ∈ Set.range (localIdeal τ hτ a).subschemeι ↔
      PELOriginalLevelPowerSections318.value τ hτ 1 (0 : Label 1) z=0 := by
    rw [PrincipalZeroComplexPoints318.point_mem,local_value τ hτ a z ha]
    rw [div_eq_zero_iff]
    exact or_iff_left (PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ a.val z
      (theta_nonzero τ hτ a z ha))
  rw [←hlocal]
  constructor
  · rintro ⟨x,hx⟩
    have he : (opens τ hτ a).ι (p (IsLocalRing.closedPoint ℂ))=
        PELOriginalThetaZeroScheme318.inclusion τ hτ x := by
      rw [←Scheme.Hom.comp_apply,hp,hx]
    obtain ⟨v,hv,hv'⟩ := Scheme.exists_preimage_of_isPullback (cartesian τ hτ a)
      (p (IsLocalRing.closedPoint ℂ)) x he
    exact ⟨v,hv⟩
  · rintro ⟨v,hv⟩
    refine ⟨chart τ hτ a v,?_⟩
    have h := congrArg (fun f => f v) (cartesian τ hτ a).w
    change (opens τ hτ a).ι ((localIdeal τ hτ a).subschemeι v)=
      PELOriginalThetaZeroScheme318.inclusion τ hτ (chart τ hτ a v) at h
    rw [hv,←Scheme.Hom.comp_apply,hp] at h
    exact h.symm

/-- Every original theta zero gives a genuine Spec(C)-valued point of
this SAME full scheme-theoretic zero locus. -/
@[expose] def originalPoint (z : ComplexVectors)
    (hz : PELOriginalLevelPowerSections318.value τ hτ 1 (0 : Label 1) z=0) :
    Spec (CommRingCat.of ℂ) ⟶ zeroScheme τ hτ :=
  ReducedSourceClosedLift318.lift (PELOriginalThetaZeroScheme318.inclusion τ hτ)
    (candidateComplexPoint τ hτ (projection (P τ) z)) (by
      rintro x ⟨y,rfl⟩
      rw [show y=IsLocalRing.closedPoint ℂ from Subsingleton.elim _ _]
      exact (support_iff τ hτ z).mpr hz)
@[reassoc] lemma originalPoint_inclusion (z : ComplexVectors)
    (hz : PELOriginalLevelPowerSections318.value τ hτ 1 (0 : Label 1) z=0) :
    originalPoint τ hτ z hz≫PELOriginalThetaZeroScheme318.inclusion τ hτ=
      candidateComplexPoint τ hτ (projection (P τ) z) :=
  ReducedSourceClosedLift318.lift_fac _ _ _

/-- ALL complex-valued points of the full theta zero scheme come from
original theta zeros, with literal equality of scheme morphisms. -/
theorem every_point (p : Spec (CommRingCat.of ℂ) ⟶ zeroScheme τ hτ)
    (hp : p≫PELOriginalThetaZeroScheme318.structureMap τ hτ=𝟙 _) :
    ∃ z : ComplexVectors,∃ hz : PELOriginalLevelPowerSections318.value τ hτ 1 (0 : Label 1) z=0,
      p=originalPoint τ hτ z hz := by
  obtain ⟨j,z,hz,he⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ
    (p≫PELOriginalThetaZeroScheme318.inclusion τ hτ) hp
  rw [PELOriginalChartSchemePointIdentity318.chart_point] at he
  have hzero : PELOriginalLevelPowerSections318.value τ hτ 1 (0 : Label 1) z=0 := by
    apply (support_iff τ hτ z).mp
    refine ⟨p (IsLocalRing.closedPoint ℂ),?_⟩
    exact congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) he
  refine ⟨z,hzero,?_⟩
  apply (cancel_mono (PELOriginalThetaZeroScheme318.inclusion τ hτ)).1
  rw [originalPoint_inclusion]
  exact he
end PELOriginalThetaZeroComplexPoints318
