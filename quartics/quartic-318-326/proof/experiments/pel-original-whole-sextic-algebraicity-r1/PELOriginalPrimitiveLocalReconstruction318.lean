module
public import PELOriginalLocalizedEvaluationSquare318
public import MonogenicOriginalCoordinates318
public import LocalizedPrimitiveRootChart318
public section
noncomputable section
namespace PELOriginalPrimitiveLocalReconstruction318
open Set Filter Polynomial
open scoped Topology
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLevelThreeLocalImage318
open PELOriginalLocalizedEvaluationSquare318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- This is the actual original regular primitive coordinate, evaluated
by the whole localization map. The total extension outside its domain
plays no role in the neighborhood statements below. -/
@[expose] def primitiveValue (z : ComplexVectors) : ℂ :=
  PELOriginalLocalizedEvaluationRegularity318.evaluate τ hτ j
    (polynomialMap τ hτ j x d) (e (AdjoinRoot.root Q)) z

lemma primitiveValue_eq (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0)
    (hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0) :
    primitiveValue τ hτ j x d Q e z =
      (originalPoint τ hτ j x z hz d hv).val (e (AdjoinRoot.root Q)) := by
  have hd : algebraEvaluation τ hτ z j hz (polynomialMap τ hτ j x d) ≠ 0 := by
    rwa [polynomial_evaluation]
  exact PELOriginalLocalizedEvaluationRegularity318.evaluate_on_open
    τ hτ j _ _ z hz hd

lemma original_root (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0)
    (hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0) :
    LocalizedPrimitiveRootChart318.equation d Q
      (projectedVector τ hτ j x z, primitiveValue τ hτ j x d Q e z) = 0 := by
  rw [LocalizedPrimitiveRootChart318.equation_on_open d Q _ hv,
    primitiveValue_eq τ hτ j x d Q e z hz hv]
  exact AdjoinRootSpecializedPoints318.point_root Q _
    (BasePreservingAffinePoints318.monogenicPointsEquiv _ _ Q e he
      (originalPoint τ hτ j x z hz d hv))

/-- At EVERY original point over the common separable base open, the
full original projective-chart map locally factors through the SAME
fixed projected pair. Every coordinate expression comes from the whole
original quotient order. The local branch is selected by ambient root
uniqueness and the genuine continuity of the actual primitive function. -/
theorem exists_local_reconstruction (hs : Q.Separable) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0)
    (hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0) :
    ∃ G : ComplexVectors → TargetModel 1,
      DifferentiableAt ℂ G (projectedVector τ hτ j x z) ∧
      ratioVector τ hτ 1 j =ᶠ[𝓝 z] fun w => G (projectedVector τ hτ j x w) := by
  let p := projectedVector τ hτ j x
  let b := primitiveValue τ hτ j x d Q e
  have hp : ContDiffAt ℂ 1 p z :=
    (localProjection τ hτ x j).contDiff.contDiffAt.comp z
      (PELOriginalLevelThetaStrictDerivative318.ratio_contDiffAt τ hτ 1 j z hz)
  have hd : algebraEvaluation τ hτ z j hz (polynomialMap τ hτ j x d) ≠ 0 := by
    rwa [polynomial_evaluation]
  have hb : ContDiffAt ℂ 1 b z :=
    PELOriginalLocalizedEvaluationRegularity318.contDiffAt_evaluate τ hτ j
      (polynomialMap τ hτ j x d) (e (AdjoinRoot.root Q)) z hz hd
  have hr := original_root τ hτ j x d Q e he z hz hv
  have hrs : (Q.map (ComplexPolynomialOpenPoints318.evaluation d (p z) hv)).eval (b z) = 0 := by
    rw [←LocalizedPrimitiveRootChart318.equation_on_open d Q (p z) hv]
    exact hr
  obtain ⟨g,hg,hg0,hge,hgu⟩ :=
    LocalizedPrimitiveRootChart318.exists_root_graph d Q hs (p z) hv (b z) hrs
  have hpair : ContinuousAt (fun w => (p w,b w)) z :=
    hp.continuousAt.prodMk hb.continuousAt
  have hvalid : ∀ᶠ w in 𝓝 z, value τ hτ 3 j w ≠ 0 ∧ MvPolynomial.eval (p w) d ≠ 0 := by
    have hc := ((AnalyticOnNhd.eval_mvPolynomial d) (p z) (mem_univ _)).continuousAt.comp
      hp.continuousAt
    filter_upwards [(PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hz,
      hc.eventually_ne hv] with w hw hwv
    exact ⟨hw,hwv⟩
  have hbranch : ∀ᶠ w in 𝓝 z, g (p w) = b w := by
    filter_upwards [hpair.tendsto.eventually hgu,hvalid] with w hu hw
    exact hu.mp (original_root τ hτ j x d Q e he w hw.1 hw.2)
  have hrep (a : TargetIndex) := MonogenicOriginalCoordinates318.exists_expression
    (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d) Q e he
    (algebraMap (CoordinateChart τ hτ j) _ (coordinateElement τ hτ j a))
  choose P hP hPeval using hrep
  let G : ComplexVectors → TargetModel 1 :=
    fun v a => LocalizedPrimitiveRootChart318.equation d (P a) (v,g v)
  refine ⟨G,?_,?_⟩
  · apply differentiableAt_pi.mpr
    intro a
    exact ((LocalizedPrimitiveRootChart318.equation_analytic d (P a) (p z) hv (g (p z))).comp
      (analyticAt_id.prod hg)).differentiableAt
  · filter_upwards [hvalid,hbranch] with w hw hbw
    funext a
    have hformula := hPeval a _ (originalPoint τ hτ j x w hw.1 d hw.2)
    rw [originalPoint_source,coordinate_evaluation] at hformula
    change ratioVector τ hτ 1 j w a =
      LocalizedPrimitiveRootChart318.equation d (P a) (p w,g (p w))
    rw [LocalizedPrimitiveRootChart318.equation_on_open d (P a) (p w) hw.2,
      Polynomial.eval_map,hbw,primitiveValue_eq τ hτ j x d Q e w hw.1 hw.2]
    exact hformula
end PELOriginalPrimitiveLocalReconstruction318
