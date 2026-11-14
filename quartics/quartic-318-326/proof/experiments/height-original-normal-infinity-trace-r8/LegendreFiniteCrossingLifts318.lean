module
public import LegendreLiteralFiniteBranch318
public import SimpleBranchCrossingPaths318
public section
noncomputable section
namespace LegendreFiniteCrossingLifts318
open Set Filter
open scoped Topology
open LegendreSimpleBranchCharts318 LegendreHalfPlaneAnalyticSheets318
open SimpleBranchCrossingPaths318
set_option maxHeartbeats 1200000
variable (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3)

@[expose] def lift (upper:Bool) (s t:ℝ) : ℂ :=
  (LegendreLiteralFiniteBranch318.point l h0 h1 j (rootArc upper s t)).val.2
lemma branch_real (hl:l.im=0) : ((branch l j).re:ℂ)=branch l j := by
  apply Complex.ext
  · simp
  · fin_cases j <;> simp [branch,hl]

/-- Actual coordinate equation for the complete explicit crossing lift. -/
lemma lift_square (hl:l.im=0) (upper:Bool) (s t:ℝ) :
    lift l h0 h1 j upper s t^2=
      polynomial l (baseArc (branch l j).re upper s t) := by
  have he:=(LegendreLiteralFiniteBranch318.point l h0 h1 j (rootArc upper s t)).property
  simpa only [lift,LegendreLiteralFiniteBranch318.point,baseArc,branch_real l j hl] using he
lemma lift_start (s:ℝ) : lift l h0 h1 j false s 0=lift l h0 h1 j true s 0 := by
  simp only [lift,rootArc_start]
lemma lift_opposite_end (s:ℝ) : lift l h0 h1 j false s 1= -lift l h0 h1 j true s 1 := by
  simp only [lift,LegendreLiteralFiniteBranch318.point,opposite_endpoints,neg_sq,neg_mul]

/-- Arbitrarily small complete actual target crossings, continuous at
BOTH real endpoints and throughout each interior, with a common nonzero
right lift and opposite nonzero left lifts. The scale is constructed from
the same genuine target chart's analytic and unit neighborhoods. -/
theorem exists_crossing (δ:ℝ) (hδ:0<δ) :
    ∃s:ℝ,0<s ∧ s<δ ∧
      (∀upper,ContinuousOn (lift l h0 h1 j upper s) (Icc 0 1)) ∧
      (∀upper t,t∈Icc 0 1 → ContinuousAt (lift l h0 h1 j upper s) t) ∧
      (∀upper t,t∈Icc 0 1 → lift l h0 h1 j upper s t≠0) := by
  let c:ℂ→ℂ×ℂ:=fun w=>(LegendreLiteralFiniteBranch318.point l h0 h1 j w).val
  let h:ℂ→ℂ:=fun w=>LegendreLiteralFiniteBranch318.root l h0 h1 j (branch l j+w^2)
  have hc:AnalyticAt ℂ c 0:=LegendreLiteralFiniteBranch318.point_coordinates_analytic l h0 h1 j
  have hh:ContinuousAt h 0:=by
    have ht:ContinuousAt (fun w:ℂ=>branch l j+w^2) 0:=by fun_prop
    exact (by simpa using (LegendreLiteralFiniteBranch318.root_analytic l h0 h1 j).continuousAt).comp ht
  have hh0:h 0≠0:=by simpa only [h,zero_pow (by decide : 2≠0),add_zero] using
    LegendreLiteralFiniteBranch318.root_center_ne l h0 h1 j
  let U:Set ℂ:={w|AnalyticAt ℂ c w ∧ h w≠0 ∧ ‖w‖<δ}
  have hU:U∈𝓝 (0:ℂ):=by
    have hb:∀ᶠ w in 𝓝 (0:ℂ),‖w‖<δ:=by
      simpa only [Metric.mem_ball,dist_zero_right] using Metric.ball_mem_nhds (0:ℂ) hδ
    exact hc.eventually_analyticAt.and ((hh.eventually_ne hh0).and hb)
  obtain ⟨s,hs,hpath⟩:=exists_small_crossing hU
  have hsδ:s<δ:=by
    have hh:‖rootArc true s 0‖<δ:=(hpath true 0 ⟨le_rfl,by norm_num⟩).2.2
    simpa only [rootArc_start,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs] using hh
  have hcont:∀upper t,t∈Icc 0 1 → ContinuousAt (lift l h0 h1 j upper s) t:=by
    intro upper t ht
    exact ((hpath upper t ht).1.continuousAt.snd).comp
      (rootArc_continuous upper s).continuousAt
  refine ⟨s,hs,hsδ,fun upper t ht=>(hcont upper t ht).continuousWithinAt,hcont,?_⟩
  intro upper t ht
  change rootArc upper s t*h (rootArc upper s t)≠0
  exact mul_ne_zero (rootArc_nonzero upper s t hs ht) (hpath upper t ht).2.1
end LegendreFiniteCrossingLifts318
