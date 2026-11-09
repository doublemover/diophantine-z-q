module
public import ActualThreeQuotientHolomorphic318
public import ActualThreeCuspAnalytic318
public section
noncomputable section
open Function Filter Topology
open scoped OnePoint
namespace ActualThreeFilledHolomorphic318
open GammaOneFiber318 PeterssonQuotient318 ActualThreeExceptionalParameter318
open ActualThreeCuspFilling318 ActualThreeCuspOverlap318 ActualThreeCuspExhaustion318
open ActualThreeSphereCharts318 ActualThreeFilledParameter318 ActualThreeCuspAnalytic318
open ActualThreeQuotientHolomorphic318 FiniteCuspEnds318 ActualThreeQParameter318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An arbitrary function on the actual filling, expressed on the independent
standard sphere using the proved original compact comparison. -/
@[expose] def targetExpression (u : Filled → ℂ) (z : OnePoint ℂ) : ℂ :=
  u (compactHomeomorph.symm z)

lemma targetExpression_original (u : Filled → ℂ) (b : Base (image 3)) :
    targetExpression u (quotientParameter b : OnePoint ℂ)=u (original b) := by
  rw [←compactHomeomorph_original]
  exact congrArg u (compactHomeomorph.symm_apply_apply _)

/-- The standard inverse target chart at the assigned boundary point: 1/t at
infinity (with t=0 sent to infinity), and the ordinary finite chart at zero. -/
@[expose] def inverseSphereChart (c : End 3) (t : ℂ) : OnePoint ℂ :=
  if c=infinityEnd then if t=0 then ∞ else (t⁻¹ : ℂ) else t

/-- Total extension of the actual source disc map. Its arbitrary values
outside the disc are irrelevant to its germ at the actual origin. -/
@[expose] def sourceDisc (c : End 3) (q : ℂ) : Filled := by
  classical
  exact if hq : q ∈ disc c then cuspChart c ⟨q,hq⟩ else cusp c

lemma sphereChart_eq_inverse (c : End 3) {q : ℂ} (hq : q ∈ disc c) :
    sphereChart c q = inverseSphereChart c (endCoordinate c q) := by
  by_cases hz : q=0
  · subst q
    rw [sphereChart_zero,endCoordinate_zero]
    rcases end_exhaustion c with rfl | rfl <;>
      simp [inverseSphereChart,boundaryValue,ends_distinct.symm]
  · have hn := qParameter_ne_zero (representative 3 c) ⟨hz,hq⟩
    rw [sphereChart_nonzero c hz]
    rcases end_exhaustion c with rfl | rfl <;>
      simp [inverseSphereChart,endCoordinate,ends_distinct.symm,hn]

lemma target_source_disc (u : Filled → ℂ) (c : End 3) :
    (fun q => u (sourceDisc c q)) =ᶠ[𝓝 (0:ℂ)]
      (fun q => targetExpression u (inverseSphereChart c (endCoordinate c q))) := by
  have hd : ∀ᶠ q in 𝓝 (0:ℂ), q ∈ disc c :=
    (disc_open c).mem_nhds (zeroPoint c).property
  filter_upwards [hd] with q hq
  rw [sourceDisc,dite_eq_left hq,←sphereChart_eq_inverse c hq,
    ←filledParameter_disc c ⟨q,hq⟩,←compactHomeomorph_apply]
  exact (congrArg u (compactHomeomorph.symm_apply_apply _)).symm

/-- Exact local holomorphic comparison at every original point, including
elliptic points, against the independently defined original quotient pullback. -/
theorem original_holomorphic_iff (u : Filled → ℂ) (b : Base (image 3)) :
    QuotientHolomorphicAt (u ∘ original) b ↔
      AnalyticAt ℂ (fun t : ℂ => targetExpression u (t : OnePoint ℂ)) (quotientParameter b) := by
  have he : (fun t : ℂ => targetExpression u (t : OnePoint ℂ)) =ᶠ[𝓝 (quotientParameter b)]
      parameterExpression (u ∘ original) := by
    filter_upwards [eventually_ne_nhds (quotientParameter_ne_zero b)] with t ht
    obtain ⟨a,ha⟩ := ActualThreeParameterProper318.fullParameter_surjective ⟨t,ht⟩
    have hae : quotientParameter a=t := congrArg Subtype.val ha
    rw [←hae,targetExpression_original,expression_parameter]
    rfl
  rw [quotientHolomorphicAt_iff_parameter]
  exact ⟨fun h => h.congr he.symm,fun h => h.congr he⟩

/-- Exact local holomorphic comparison at every added source cusp, using its
actual selected q disc and the independent ordinary target sphere chart. -/
theorem cusp_holomorphic_iff (u : Filled → ℂ) (c : End 3) :
    AnalyticAt ℂ (fun q => u (sourceDisc c q)) 0 ↔
      AnalyticAt ℂ (fun t => targetExpression u (inverseSphereChart c t)) 0 := by
  let g : ℂ → ℂ := fun t => targetExpression u (inverseSphereChart c t)
  have he := target_source_disc u c
  constructor
  · intro hu
    have hp : AnalyticAt ℂ (g ∘ endCoordinate c) 0 := hu.congr he
    simpa only [endCoordinate_zero] using HolomorphicDescent318.analyticAt_of_comp_regular
      (endCoordinate_analytic c) hp (endCoordinate_deriv_ne_zero c)
  · intro hg
    have hp : AnalyticAt ℂ (g ∘ endCoordinate c) 0 :=
      hg.comp_of_eq (endCoordinate_analytic c) (endCoordinate_zero c)
    exact hp.congr he.symm

/-- These two genuine source germ tests cover every point of the actual
compact filling, with no missing exceptional points or added cusp origins. -/
theorem every_point_has_source_germ (z : Filled) :
    (∃ b : Base (image 3), original b=z) ∨ (∃ c : End 3, cusp c=z) :=
  original_or_cusp z

end ActualThreeFilledHolomorphic318
