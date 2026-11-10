module
public import ActualThreeInfinityUniformizer318
public section
noncomputable section
open Filter Topology
open scoped MatrixGroups
namespace ActualThreeCuspAssignment318
open ActualThreeQOrders318 ActualThreeQParameter318 ActualThreeQMeromorphic318
open ActualThreeInfinityUniformizer318 ActualThreeCuspHomeomorph318 WidthQParameter318
open ActualThreeExceptionalParameter318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma cusp_parameter_ranges_disjoint {q r : ℂ}
    (hq : q ∈ punctured (wReal 1) 2) (hr : r ∈ punctured (wReal ModularGroup.S) 2) :
    qParameter 1 q ≠ qParameter ModularGroup.S r := by
  intro he
  rw [show qParameter 1 q = _ from qParameter_coe 1 ⟨q,hq⟩,
    show qParameter ModularGroup.S r = _ from qParameter_coe ModularGroup.S ⟨r,hr⟩] at he
  have hb := ActualThreeGlobalParameter318.fullParameter_injective (Subtype.ext he)
  have h1 := ((cuspHomeomorph 1).symm ⟨q,hq⟩).property
  rw [hb] at h1
  exact Set.disjoint_left.mp ActualThreeCuspWidths318.neighborhoods_disjoint h1
    ((cuspHomeomorph ModularGroup.S).symm ⟨r,hr⟩).property

/-- Global injectivity and the two disjoint genuine cusp neighborhoods exclude
sending both source cusps to the infinite target cusp. The simple reciprocal
coordinate at the first cusp supplies the actual local inverse used here. -/
theorem S_order_not_negative_three : meromorphicOrderAt (qParameter ModularGroup.S) 0 ≠ -3 := by
  intro ho
  have hn : deriv reciprocalInfinity 0 ≠ 0 := by rw [reciprocalInfinity_deriv]; exact one_ne_zero
  let r := reciprocalInfinity_analytic.hasStrictDerivAt.localInverse _ _ _ hn
  have hr : AnalyticAt ℂ r 0 := by
    simpa only [reciprocalInfinity_zero] using reciprocalInfinity_analytic.analyticAt_localInverse hn
  have hr0 : r 0 = 0 := by
    have h := HasStrictFDerivAt.localInverse_apply_image
      (reciprocalInfinity_analytic.hasStrictDerivAt.hasStrictFDerivAt_equiv hn)
    simpa only [reciprocalInfinity_zero] using h
  have hright : ∀ᶠ s in 𝓝 (0:ℂ), reciprocalInfinity (r s) = s := by
    simpa only [reciprocalInfinity_zero] using HasStrictDerivAt.eventually_right_inverse
      (hf:=reciprocalInfinity_analytic.hasStrictDerivAt) (hf':=hn)
  have hsmall : ∀ᶠ s in 𝓝 (0:ℂ), ‖r s‖ < radius (wReal 1) 2 := by
    apply hr.continuousAt.norm.eventually (p:=fun x : ℝ => x < radius (wReal 1) 2)
    apply isOpen_Iio.mem_nhds
    change ‖r 0‖ < radius (wReal 1) 2
    rw [hr0,norm_zero]
    exact radius_positive _ _
  have hlim : Tendsto (fun q => (qParameter ModularGroup.S q)⁻¹) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    apply tendsto_zero_of_meromorphicOrderAt_pos
    change 0 < meromorphicOrderAt ((qParameter ModularGroup.S)⁻¹) 0
    rw [meromorphicOrderAt_inv,ho]
    norm_num
  have hf : ∀ᶠ q in 𝓝[≠] (0:ℂ), False := by
    filter_upwards [eventually_punctured ModularGroup.S,hlim.eventually hright,hlim.eventually hsmall]
      with q hq hrightq hsmallq
    have hs : (qParameter ModularGroup.S q)⁻¹ ≠ 0 := inv_ne_zero (qParameter_ne_zero _ hq)
    have hrne : r ((qParameter ModularGroup.S q)⁻¹) ≠ 0 := by
      intro hz
      rw [hz,reciprocalInfinity_zero] at hrightq
      exact hs hrightq.symm
    apply cusp_parameter_ranges_disjoint ⟨hrne,hsmallq⟩ hq
    apply inv_injective
    exact hrightq
  obtain ⟨q,hq⟩ := hf.exists
  exact hq

/-- The actual S cusp maps to T=0 with simple zero in its own width-three q. -/
theorem S_order : meromorphicOrderAt (qParameter ModularGroup.S) 0 = 1 :=
  S_order_cases.resolve_left S_order_not_negative_three

lemma S_zero : qParameter ModularGroup.S 0 = 0 := by
  simp [qParameter,punctured]

/-- The original T germ extends analytically by zero at the actual S cusp. -/
theorem S_analytic : AnalyticAt ℂ (qParameter ModularGroup.S) 0 := by
  apply AnalyticAt.of_meromorphicOrderAt_pos
  · rw [S_order]
    norm_num
  · exact S_zero

/-- An analytic scalar germ of order one is a genuine local uniformizer. -/
lemma deriv_ne_zero_of_order_one {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (ho : meromorphicOrderAt f 0 = 1) : deriv f 0 ≠ 0 := by
  obtain ⟨u,hu,hu0,he⟩ := (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).mp ho
  have he' : f =ᶠ[𝓝[≠] (0:ℂ)] (fun q => q*u q) := by
    simpa only [sub_zero,zpow_one,smul_eq_mul] using! he
  have hefull : f =ᶠ[𝓝 (0:ℂ)] (fun q => q*u q) :=
    (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hf.continuousAt
      (analyticAt_id.mul hu).continuousAt).mp he'
  have hd : HasDerivAt (fun q : ℂ => q*u q) (u 0) 0 := by
    simpa using! (hasDerivAt_id (0:ℂ)).mul hu.differentiableAt.hasDerivAt
  rw [(hd.congr_of_eventuallyEq hefull).deriv]
  exact hu0

/-- T itself is a genuine local analytic coordinate at the actual S cusp. -/
theorem S_deriv_ne_zero : deriv (qParameter ModularGroup.S) 0 ≠ 0 :=
  deriv_ne_zero_of_order_one S_analytic S_order

end ActualThreeCuspAssignment318
