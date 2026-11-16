module
public import RiemannNormalizedInterior318
public section
noncomputable section
namespace RiemannNormalizedUniqueness318
open Set Metric Filter Topology
set_option maxHeartbeats 3000000

/-- The transition of the two ACTUAL conformal charts, with the first
chart's genuine analytic inverse. -/
@[expose] def transition (e g : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ :=
  fun w => g (e.symm w)

section Transition
variable (e g : OpenPartialHomeomorph ℂ ℂ) {U : Set ℂ}
    (heS : e.source=U) (hgS : g.source=U)
    (heT : e.target=ball 0 1) (hgT : g.target=ball 0 1)
    (hgA : ∀ z∈U,AnalyticAt ℂ g z)
    (heI : ∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w)

include heS hgS heT hgT hgA heI in
theorem transition_analytic {w : ℂ} (hw : w∈ball (0:ℂ) 1) :
    AnalyticAt ℂ (transition e g) w := by
  have hwt : w∈e.target := heT.symm ▸ hw
  exact (hgA (e.symm w) (heS ▸ e.map_target hwt)).comp (heI w hw)

include heS hgS heT hgT in
theorem transition_maps : MapsTo (transition e g) (ball 0 1) (ball 0 1) := by
  intro w hw
  have hx : e.symm w∈g.source := hgS.symm ▸ (heS ▸ e.map_target (heT.symm ▸ hw))
  exact hgT ▸ g.map_source hx
end Transition

/-- Product form of the transition derivative, avoiding an unproved
choice of inverse derivative or affine lift. -/
theorem transition_derivative_mul (e g : OpenPartialHomeomorph ℂ ℂ) {U : Set ℂ}
    (heS : e.source=U) (hgS : g.source=U)
    (heT : e.target=ball 0 1) (hgT : g.target=ball 0 1)
    (heA : ∀ z∈U,AnalyticAt ℂ e z) (hgA : ∀ z∈U,AnalyticAt ℂ g z)
    (heI : ∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w)
    {z₀ : ℂ} (hz : z₀∈U) (he0 : e z₀=0) :
    deriv (transition e g) 0*deriv e z₀=deriv g z₀ := by
  have ha := transition_analytic e g heS hgS heT hgT hgA heI (by simp : (0:ℂ)∈ball 0 1)
  have ha' : AnalyticAt ℂ (transition e g) (e z₀) := he0.symm ▸ ha
  have hc := ha'.differentiableAt.hasDerivAt.comp z₀ (heA z₀ hz).differentiableAt.hasDerivAt
  rw [he0] at hc
  have heq : g=ᶠ[𝓝 z₀] (fun z => transition e g (e z)) := by
    filter_upwards [e.open_source.mem_nhds (heS.symm ▸ hz)] with z hzu
    simp only [transition,e.left_inv hzu]
  exact (hc.congr_of_eventuallyEq heq).unique (hgA z₀ hz).differentiableAt.hasDerivAt

/-- Schwarz bounds in the forward transition imply monotonicity of the
original derivatives' norms. The reverse transition will give equality. -/
theorem derivative_norm_le (e g : OpenPartialHomeomorph ℂ ℂ) {U : Set ℂ}
    (heS : e.source=U) (hgS : g.source=U)
    (heT : e.target=ball 0 1) (hgT : g.target=ball 0 1)
    (heA : ∀ z∈U,AnalyticAt ℂ e z) (hgA : ∀ z∈U,AnalyticAt ℂ g z)
    (heI : ∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w)
    {z₀ : ℂ} (hz : z₀∈U) (he0 : e z₀=0) (hg0 : g z₀=0) :
    ‖deriv g z₀‖≤‖deriv e z₀‖ := by
  have hinv : e.symm 0=z₀ := by rw [←he0]; exact e.left_inv (heS.symm ▸ hz)
  have ht0 : transition e g 0=0 := by simp only [transition,hinv,hg0]
  have hmaps : MapsTo (transition e g) (ball 0 1) (closedBall (transition e g 0) 1) := by
    rw [ht0]
    intro w hw
    exact ball_subset_closedBall (transition_maps e g heS hgS heT hgT hw)
  have hbound := Complex.norm_deriv_le_one_of_mapsTo_ball
    (fun w hw => (transition_analytic e g heS hgS heT hgT hgA heI hw).differentiableAt.differentiableWithinAt)
    hmaps (by norm_num : (0:ℝ)<1)
  have hd := congrArg norm (transition_derivative_mul e g heS hgS heT hgT heA hgA heI hz he0)
  rw [norm_mul] at hd
  nlinarith [norm_nonneg (deriv e z₀)]

/-- Normalization by value zero and positive real derivative makes the
interior conformal chart unique on the original source. -/
theorem normalized_unique (e g : OpenPartialHomeomorph ℂ ℂ) {U : Set ℂ}
    (heS : e.source=U) (hgS : g.source=U)
    (heT : e.target=ball 0 1) (hgT : g.target=ball 0 1)
    (heA : ∀ z∈U,AnalyticAt ℂ e z) (hgA : ∀ z∈U,AnalyticAt ℂ g z)
    (heI : ∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w)
    (hgI : ∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ g.symm w)
    {z₀ : ℂ} (hz : z₀∈U) (he0 : e z₀=0) (hg0 : g z₀=0)
    (hei : (deriv e z₀).im=0) (hgi : (deriv g z₀).im=0)
    (her : 0<(deriv e z₀).re) (hgr : 0<(deriv g z₀).re) : EqOn e g U := by
  have hn := le_antisymm
    (derivative_norm_le e g heS hgS heT hgT heA hgA heI hz he0 hg0)
    (derivative_norm_le g e hgS heS hgT heT hgA heA hgI hz hg0 he0)
  have heReal : deriv e z₀=((deriv e z₀).re:ℂ) := by apply Complex.ext <;> simp [hei]
  have hgReal : deriv g z₀=((deriv g z₀).re:ℂ) := by apply Complex.ext <;> simp [hgi]
  have hd : deriv g z₀=deriv e z₀ := by
    rw [hgReal,heReal,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hgr,abs_of_pos her] at hn
    rw [hgReal,heReal,hn]
  have hne : deriv e z₀≠0 := by intro h; rw [h] at her; exact lt_irrefl 0 her
  have hfder : deriv (transition e g) 0=1 := by
    have hh := transition_derivative_mul e g heS hgS heT hgT heA hgA heI hz he0
    rw [hd] at hh
    exact mul_right_cancel₀ hne (by simpa only [one_mul] using hh)
  have hinv : e.symm 0=z₀ := by rw [←he0]; exact e.left_inv (heS.symm ▸ hz)
  have hf0 : transition e g 0=0 := by simp only [transition,hinv,hg0]
  have hmaps : MapsTo (transition e g) (ball 0 1) (closedBall (transition e g 0) 1) := by
    rw [hf0]
    intro w hw
    exact ball_subset_closedBall (transition_maps e g heS hgS heT hgT hw)
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    (fun w hw => (transition_analytic e g heS hgS heT hgT hgA heI hw).differentiableAt.differentiableWithinAt)
    hmaps (by simp : (0:ℂ)∈ball 0 1) (by simpa [hfder] : ‖dslope (transition e g) 0 0‖=(1:ℝ)/1)
  intro z hzu
  have hw : e z∈ball (0:ℂ) 1 := heT ▸ e.map_source (heS.symm ▸ hzu)
  have hh := haff hw
  simp [hf0,hfder] at hh
  change g (e.symm (e z))=e z at hh
  rw [e.left_inv (heS.symm ▸ hzu)] at hh
  exact hh.symm
end RiemannNormalizedUniqueness318
