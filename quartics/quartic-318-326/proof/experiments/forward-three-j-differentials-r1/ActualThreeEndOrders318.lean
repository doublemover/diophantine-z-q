module
public import ActualThreeCuspAssignment318
public import ActualThreeCuspHausdorff318
public section
noncomputable section
open Filter Topology
open scoped MatrixGroups
namespace ActualThreeEndOrders318
open ActualThreeQOrders318 ActualThreeQParameter318 ActualThreeQMeromorphic318
open ActualThreeInfinityUniformizer318 ActualThreeCuspHomeomorph318 WidthQParameter318
open ActualThreeExceptionalParameter318 ActualThreeCuspExhaustion318 FiniteCuspEnds318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma parameter_ranges_disjoint (g : SL(2,ℤ))
    (hdisj : Disjoint (RotatedProjection318.neighborhood 3 1) (RotatedProjection318.neighborhood 3 g)) {q r : ℂ}
    (hq : q ∈ punctured (wReal 1) 2) (hr : r ∈ punctured (wReal g) 2) :
    qParameter 1 q ≠ qParameter g r := by
  intro he
  rw [show qParameter 1 q = _ from qParameter_coe 1 ⟨q,hq⟩,
    show qParameter g r = _ from qParameter_coe g ⟨r,hr⟩] at he
  have hb := ActualThreeGlobalParameter318.fullParameter_injective (Subtype.ext he)
  have h1 := ((cuspHomeomorph 1).symm ⟨q,hq⟩).property
  rw [hb] at h1
  exact Set.disjoint_left.mp hdisj h1
    ((cuspHomeomorph g).symm ⟨r,hr⟩).property

/-- Global injectivity and the two disjoint genuine cusp neighborhoods exclude
sending both source cusps to the infinite target cusp. The simple reciprocal
coordinate at the first cusp supplies the actual local inverse used here. -/
theorem order_not_negative_three_of_disjoint (g : SL(2,ℤ))
    (hdisj : Disjoint (RotatedProjection318.neighborhood 3 1) (RotatedProjection318.neighborhood 3 g)) : meromorphicOrderAt (qParameter g) 0 ≠ -3 := by
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
  have hlim : Tendsto (fun q => (qParameter g q)⁻¹) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    apply tendsto_zero_of_meromorphicOrderAt_pos
    change 0 < meromorphicOrderAt ((qParameter g)⁻¹) 0
    rw [meromorphicOrderAt_inv,ho]
    norm_num
  have hf : ∀ᶠ q in 𝓝[≠] (0:ℂ), False := by
    filter_upwards [eventually_punctured g,hlim.eventually hright,hlim.eventually hsmall]
      with q hq hrightq hsmallq
    have hs : (qParameter g q)⁻¹ ≠ 0 := inv_ne_zero (qParameter_ne_zero _ hq)
    have hrne : r ((qParameter g q)⁻¹) ≠ 0 := by
      intro hz
      rw [hz,reciprocalInfinity_zero] at hrightq
      exact hs hrightq.symm
    apply parameter_ranges_disjoint g hdisj ⟨hrne,hsmallq⟩ hq
    apply inv_injective
    exact hrightq
  obtain ⟨q,hq⟩ := hf.exists
  exact hq


lemma representative_infinity_region :
    RotatedProjection318.neighborhood 3 (representative 3 infinityEnd) =
      RotatedProjection318.neighborhood 3 1 := representative_region 3 infinityEnd

lemma representative_zero_region :
    RotatedProjection318.neighborhood 3 (representative 3 zeroEnd) =
      RotatedProjection318.neighborhood 3 ModularGroup.S := representative_region 3 zeroEnd

lemma representative_width_infinity : ActualThreeCuspJ318.natWidth (representative 3 infinityEnd) = 1 := by
  have h := GammaHCuspWidths318.width_of_periods_eq 3 (by decide) _ _
    (GammaHCuspWidths318.periods_of_neighborhood_eq 3 _ _ representative_infinity_region)
  exact h.trans ActualThreeCuspWidths318.width_identity

lemma representative_width_zero : ActualThreeCuspJ318.natWidth (representative 3 zeroEnd) = 3 := by
  have h := GammaHCuspWidths318.width_of_periods_eq 3 (by decide) _ _
    (GammaHCuspWidths318.periods_of_neighborhood_eq 3 _ _ representative_zero_region)
  exact h.trans ActualThreeCuspWidths318.width_S

/-- The actual selected chart at the actual infinity end has a simple T pole. -/
theorem representative_infinity_order :
    meromorphicOrderAt (qParameter (representative 3 infinityEnd)) 0 = -1 := by
  rcases qParameter_order_cases (representative 3 infinityEnd) with h | ⟨m,hm,hw,ho⟩
  · simpa [representative_width_infinity] using h
  · rw [representative_width_infinity] at hw
    omega

/-- The actual selected chart at the other original end has a simple T zero. -/
theorem representative_zero_order :
    meromorphicOrderAt (qParameter (representative 3 zeroEnd)) 0 = 1 := by
  rcases qParameter_order_cases (representative 3 zeroEnd) with h | ⟨m,hm,hw,ho⟩
  · have hd : Disjoint (RotatedProjection318.neighborhood 3 1)
        (RotatedProjection318.neighborhood 3 (representative 3 zeroEnd)) := by
      rw [representative_zero_region]
      exact ActualThreeCuspWidths318.neighborhoods_disjoint
    apply False.elim
    apply order_not_negative_three_of_disjoint _ hd
    simpa [representative_width_zero] using h
  · rw [representative_width_zero] at hw
    have hm1 : m=1 := by omega
    simpa [hm1] using ho

end ActualThreeEndOrders318
