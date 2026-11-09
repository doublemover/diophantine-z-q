module
public import ActualThreeGlobalParameter318
public import ActualThreeCuspJ318
public import RotatedBiholomorphic318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology
open GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 RotatedProjection318 ActualThreeCuspHomeomorph318
open ActualThreeExceptionalParameter318
open scoped MatrixGroups Manifold ContDiff
namespace ActualThreeQParameter318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The original full quotient parameter evaluated in its genuine width-q chart.
The value outside the actual punctured disc is irrelevant and explicitly set to zero. -/
@[expose] def qParameter (g : SL(2,ℤ)) (q : ℂ) : ℂ := by
  classical
  exact if hq : q ∈ punctured (wReal g) 2 then
    quotientParameter ((cuspHomeomorph g).symm ⟨q,hq⟩).val else 0

lemma qParameter_coe (g : SL(2,ℤ)) (q : punctured (wReal g) 2) :
    qParameter g q = quotientParameter ((cuspHomeomorph g).symm q).val := by
  simp only [qParameter, dite_eq_left q.property]

/-- This is the actual period coordinate at every high lift, not a solution
selected merely by its rational j equation. -/
theorem qParameter_projection (g : SL(2,ℤ)) (tau : high 2) :
    qParameter g (Periodic.qParam (wReal g) tau) = periodParameter (g • tau.val) := by
  change qParameter g (qMap (wReal g) 2 (wReal_pos g) tau) = _
  rw [qParameter_coe, ←cuspHomeomorph_projection g tau, Homeomorph.symm_apply_apply]
  rfl

/-- A local logarithm of the genuine exponential q map proves analyticity
throughout the punctured chart. No quotient analytic atlas is assumed. -/
theorem qParameter_analytic (g : SL(2,ℤ)) :
    AnalyticOnNhd ℂ (qParameter g) (punctured (wReal g) 2) := by
  intro q hq
  obtain ⟨tau,htau⟩ := qMap_surjective (wReal g) 2 (wReal_pos g) (by norm_num) ⟨q,hq⟩
  have hparam : Periodic.qParam (wReal g) tau = q := congrArg Subtype.val htau
  rw [←hparam]
  let r := WidthLocalInverse318.inverse (wReal g) (wReal_pos g) (tau:ℂ)
  have hr : AnalyticAt ℂ r (Periodic.qParam (wReal g) tau) :=
    WidthLocalInverse318.inverse_analytic _ _ tau
  have hr0 : r (Periodic.qParam (wReal g) tau) = (tau:ℂ) :=
    WidthLocalInverse318.inverse_value _ _ tau
  have hp : 0 < (r (Periodic.qParam (wReal g) tau)).im := by rw [hr0]; exact tau.val.im_pos
  have hof := (UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) hp).comp
    (Periodic.qParam (wReal g) tau) hr.contDiffAt.contMDiffAt
  have hg := (RotatedBiholomorphic318.integral_smul_holomorphic g
    (ofComplex (r (Periodic.qParam (wReal g) tau)))).comp (Periodic.qParam (wReal g) tau) hof
  have hc := (periodParameter_holomorphic
    (g • ofComplex (r (Periodic.qParam (wReal g) tau)))).comp (Periodic.qParam (wReal g) tau) hg
  have ha : AnalyticAt ℂ (fun v => periodParameter (g • ofComplex (r v)))
      (Periodic.qParam (wReal g) tau) := hc.contDiffAt.analyticAt
  apply ha.congr
  have hh : ∀ᶠ v in 𝓝 (Periodic.qParam (wReal g) tau), (2:ℝ) < (r v).im := by
    apply (Complex.continuous_im.continuousAt.comp hr.continuousAt).eventually
    apply isOpen_Ioi.mem_nhds
    change (2:ℝ) < (r (Periodic.qParam (wReal g) tau)).im
    rw [hr0]
    exact tau.property
  filter_upwards [hh, WidthLocalInverse318.inverse_right (wReal g) (wReal_pos g) (tau:ℂ)] with v hv hright
  have hpos : 0 < (r v).im := lt_trans (by norm_num : (0:ℝ)<2) hv
  let t : UpperHalfPlane := ⟨r v,hpos⟩
  have ht : t ∈ high 2 := hv
  have hqt : Periodic.qParam (wReal g) t = v := hright
  symm
  calc
    qParameter g v = qParameter g (Periodic.qParam (wReal g) t) := congrArg _ hqt.symm
    _ = periodParameter (g • t) := qParameter_projection g ⟨t,ht⟩
    _ = periodParameter (g • ofComplex (r v)) := by
      congr 2
      exact (ofComplex_apply_of_im_pos hpos).symm

lemma qParameter_ne_zero (g : SL(2,ℤ)) {q : ℂ} (hq : q ∈ punctured (wReal g) 2) :
    qParameter g q ≠ 0 := by
  rw [show qParameter g q = _ from qParameter_coe g ⟨q,hq⟩]
  exact quotientParameter_ne_zero _

/-- Injectivity is inherited from the actual global quotient homeomorphism
and the actual q homeomorphism, including every exceptional j value. -/
theorem qParameter_injOn (g : SL(2,ℤ)) :
    Set.InjOn (qParameter g) (punctured (wReal g) 2) := by
  intro q hq r hr he
  rw [show qParameter g q = _ from qParameter_coe g ⟨q,hq⟩,
    show qParameter g r = _ from qParameter_coe g ⟨r,hr⟩] at he
  have hb := ActualThreeGlobalParameter318.fullParameter_injective (Subtype.ext he)
  exact congrArg Subtype.val ((cuspHomeomorph g).symm.injective (Subtype.ext hb))

theorem j_identity (g : SL(2,ℤ)) {q : ℂ} (hq : q ∈ punctured (wReal g) 2) :
    ThreeCompactParameter318.J (qParameter g q) = ActualThreeCuspJ318.jExpression g q := by
  rw [show qParameter g q = _ from qParameter_coe g ⟨q,hq⟩, quotientParameter_j]
  exact ActualThreeCuspJ318.j_in_coordinate g ⟨q,hq⟩

end ActualThreeQParameter318
