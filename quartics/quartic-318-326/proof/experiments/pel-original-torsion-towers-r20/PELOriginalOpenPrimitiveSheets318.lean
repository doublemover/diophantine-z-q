module
public import PELOriginalFixedProjectionInverse318
public import PELOriginalFiniteOpenAnalyticMeeting318
public import Mathlib.Topology.IsLocalHomeomorph
public section
noncomputable section
namespace PELOriginalOpenPrimitiveSheets318
open Set Filter
open scoped Topology
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedFiniteOpen318 PELOriginalAllLevelHolomorphicMap318
open PELOriginalLevelThreeLocalImage318 PELOriginalLocalizedEvaluationSquare318
open PELOriginalPrimitiveLocalReconstruction318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- The real original source open, defined by its theta denominator and
its SAME projected base polynomial, before any image comparison. -/
@[expose] def originalDomain : Set ComplexVectors :=
  {z | value τ hτ 3 j z ≠ 0 ∧ MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0}

lemma originalDomain_open : IsOpen (originalDomain τ hτ j x d) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hp : ContinuousAt (projectedVector τ hτ j x) z :=
    (localProjection τ hτ x j).continuous.continuousAt.comp
      (PELOriginalLevelThetaStrictDerivative318.ratio_contDiffAt τ hτ 1 j z hz.1).continuousAt
  have hd := ((AnalyticOnNhd.eval_mvPolynomial d) (projectedVector τ hτ j x z)
    (mem_univ _)).continuousAt.comp hp
  exact ((PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hz.1).and
    (hd.eventually_ne hz.2)

abbrev RootLocus := AnalyticParameterizedRootChart318.ZeroLocus
  (LocalizedPrimitiveRootChart318.equation d Q)

/-- Original theta points map into the independently topologized whole
ambient root locus using their actual regular primitive evaluation. -/
@[expose] def originalRootPoint (z : originalDomain τ hτ j x d) : RootLocus d Q :=
  ⟨(projectedVector τ hτ j x z.val, primitiveValue τ hτ j x d Q e z.val),
    original_root τ hτ j x d Q e he z.val z.property.1 z.property.2⟩

lemma originalRootPoint_continuous : Continuous (originalRootPoint τ hτ j x d Q e he) := by
  have hc : Continuous (fun z : originalDomain τ hτ j x d =>
      (projectedVector τ hτ j x z.val, primitiveValue τ hτ j x d Q e z.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hp : ContinuousAt (projectedVector τ hτ j x) z.val :=
      (localProjection τ hτ x j).continuous.continuousAt.comp
        (PELOriginalLevelThetaStrictDerivative318.ratio_contDiffAt τ hτ 1 j z.val z.property.1).continuousAt
    have hd : algebraEvaluation τ hτ z.val j z.property.1 (polynomialMap τ hτ j x d) ≠ 0 := by
      rw [polynomial_evaluation]
      exact z.property.2
    have hb := (PELOriginalLocalizedEvaluationRegularity318.contDiffAt_evaluate τ hτ j
      (polynomialMap τ hτ j x d) (e (AdjoinRoot.root Q)) z.val z.property.1 hd).continuousAt
    exact (hp.prodMk hb).comp continuous_subtype_val.continuousAt
  exact hc.subtype_mk _

/-- The actual original root map is a local homeomorphism INTO THE WHOLE
root locus. This follows by cancellation of the actual root projection
and the proved fixed original projection inverse, with genuine continuity.
No topology is transported from the original image. -/
theorem originalRootPoint_localHomeomorph (hs : Q.Separable) :
    IsLocalHomeomorph (originalRootPoint τ hτ j x d Q e he) := by
  let U := originalDomain τ hτ j x d
  let f := originalRootPoint τ hτ j x d Q e he
  let p : RootLocus d Q → ComplexVectors := fun q => q.val.1
  have hproj : IsLocalHomeomorphOn (projectedVector τ hτ j x) U := by
    intro z hz
    obtain ⟨c,hc,hce,hcs⟩ := PELOriginalFixedProjectionInverse318.fixed_projection_chart
      τ hτ j x d Q hs e he z hz.1 hz.2
    exact ⟨c,hc,funext (fun w => (hce w).symm)⟩
  have hsub : IsLocalHomeomorph (fun z : U => z.val) :=
    (originalDomain_open τ hτ j x d).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcomp : IsLocalHomeomorph (p ∘ f) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    exact hproj.comp hsub.isLocalHomeomorphOn (fun z _ => z.property)
  have hp : IsLocalHomeomorphOn p (f '' univ) := by
    rintro q ⟨z,hz,rfl⟩
    obtain ⟨c,hc,hce,hca⟩ := LocalizedPrimitiveRootChart318.exists_root_chart
      d Q hs (f z) z.property.2
    exact ⟨c,hc,funext (fun w => (hce w).symm)⟩
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  exact hcomp.isLocalHomeomorphOn.of_comp_left hp
    (fun z _ => (originalRootPoint_continuous τ hτ j x d Q e he).continuousAt)

/-- The selected ORIGINAL sheets form an actual open subset of the
independently induced whole root locus, not merely an open source. -/
theorem original_sheets_open (hs : Q.Separable) :
    IsOpen (Set.range (originalRootPoint τ hτ j x d Q e he)) := by
  simpa only [Set.image_univ] using
    (originalRootPoint_localHomeomorph τ hτ j x d Q e he hs).isOpenMap univ isOpen_univ

/-- Every produced nonzero base denominator meets the actual original
theta image. Thus the selected sheet subset is genuinely nonempty on
that SAME denominator, not merely generically expected to be nonempty. -/
theorem original_sheets_nonempty (hx : value τ hτ 3 j x ≠ 0) (hd : d ≠ 0) :
    (Set.range (originalRootPoint τ hτ j x d Q e he)).Nonempty := by
  obtain ⟨z,hz,hzd⟩ :=
    PELOriginalFiniteOpenAnalyticMeeting318.meets_original_patch τ hτ j x hx d hd
  have hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0 := by
    rwa [polynomial_evaluation] at hzd
  let w : originalDomain τ hτ j x d := ⟨z,hz,hv⟩
  exact ⟨originalRootPoint τ hτ j x d Q e he w,Set.mem_range_self w⟩
end PELOriginalOpenPrimitiveSheets318
