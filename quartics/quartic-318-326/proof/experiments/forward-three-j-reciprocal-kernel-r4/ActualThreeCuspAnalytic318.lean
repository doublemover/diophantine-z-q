module
public import ActualThreeFilledParameter318
public section
noncomputable section
open Filter Topology WithTop.LinearOrderedAddCommGroup
open scoped OnePoint
namespace ActualThreeCuspAnalytic318
open ActualThreeQParameter318 ActualThreeCuspExhaustion318 ActualThreeEndOrders318
open ActualThreeSphereCharts318 ActualThreeFilledParameter318 ActualThreeCuspOverlap318
open ActualThreeCuspFilling318 FiniteCuspEnds318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ordinary independent sphere coordinate at each assigned cusp: 1/T at
infinity, and T at zero. Values at the excluded opposite chart point are unused. -/
@[expose] def sphereCoordinate (c : End 3) (z : OnePoint ℂ) : ℂ :=
  z.elim 0 (fun t => if c=infinityEnd then t⁻¹ else t)

@[expose] def endCoordinate (c : End 3) (q : ℂ) : ℂ :=
  if c=infinityEnd then (qParameter (representative 3 c) q)⁻¹
    else qParameter (representative 3 c) q

lemma endCoordinate_zero (c : End 3) : endCoordinate c 0 = 0 := by
  simp [endCoordinate,qParameter,WidthQParameter318.punctured]

lemma sphereCoordinate_sphereChart (c : End 3) (q : ℂ) :
    sphereCoordinate c (sphereChart c q)=endCoordinate c q := by
  by_cases hq : q=0
  · subst q
    rw [sphereChart_zero,endCoordinate_zero]
    rcases end_exhaustion c with rfl | rfl <;>
      simp [sphereCoordinate,boundaryValue,ends_distinct.symm,OnePoint.elim,OnePoint.infty,OnePoint.some]
  · rw [sphereChart_nonzero c hq]
    rfl

/-- This is the exact coordinate expression of the actual compact comparison
on each actual selected source disc, including its added origin. -/
lemma compactHomeomorph_chart (c : End 3) (q : disc c) :
    sphereCoordinate c (compactHomeomorph (cuspChart c q))=endCoordinate c q.val := by
  rw [compactHomeomorph_apply,filledParameter_disc,sphereCoordinate_sphereChart]

lemma endCoordinate_order (c : End 3) : meromorphicOrderAt (endCoordinate c) 0 = 1 := by
  rcases end_exhaustion c with rfl | rfl
  · have he : endCoordinate infinityEnd = (qParameter (representative 3 infinityEnd))⁻¹ := by
      funext q; simp [endCoordinate]
    rw [he,meromorphicOrderAt_inv,representative_infinity_order]
    norm_num
  · have he : endCoordinate zeroEnd = qParameter (representative 3 zeroEnd) := by
      funext q; simp [endCoordinate,ends_distinct.symm]
    rw [he,representative_zero_order]

/-- The actual source-to-target coordinate change is holomorphic at every
selected cusp, with no pole hidden by the sphere notation. -/
theorem endCoordinate_analytic (c : End 3) : AnalyticAt ℂ (endCoordinate c) 0 := by
  apply AnalyticAt.of_meromorphicOrderAt_pos
  · rw [endCoordinate_order]; norm_num
  · exact endCoordinate_zero c

theorem endCoordinate_deriv_ne_zero (c : End 3) : deriv (endCoordinate c) 0 ≠ 0 :=
  ActualThreeCuspAssignment318.deriv_ne_zero_of_order_one
    (endCoordinate_analytic c) (endCoordinate_order c)

/-- Both directions of the actual source-q / target-T coordinate change are
holomorphic near each origin; the inverse is the genuine analytic local inverse. -/
theorem exists_analytic_coordinate_inverse (c : End 3) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ r 0=0 ∧
      (∀ᶠ q in 𝓝 (0:ℂ), r (endCoordinate c q)=q) ∧
      (∀ᶠ t in 𝓝 (0:ℂ), endCoordinate c (r t)=t) := by
  let hf := endCoordinate_analytic c
  let hd := endCoordinate_deriv_ne_zero c
  let r := hf.hasStrictDerivAt.localInverse _ _ _ hd
  refine ⟨r,?_,?_,?_,?_⟩
  · simpa only [endCoordinate_zero] using hf.analyticAt_localInverse hd
  · simpa only [endCoordinate_zero] using
      HasStrictFDerivAt.localInverse_apply_image (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
  · exact HasStrictDerivAt.eventually_left_inverse (hf:=hf.hasStrictDerivAt) (hf':=hd)
  · simpa only [endCoordinate_zero] using
      HasStrictDerivAt.eventually_right_inverse (hf:=hf.hasStrictDerivAt) (hf':=hd)

end ActualThreeCuspAnalytic318
