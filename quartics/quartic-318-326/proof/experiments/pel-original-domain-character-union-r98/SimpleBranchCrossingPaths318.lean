module
public import LegendreHalfPlaneAnalyticSheets318
public section
noncomputable section
namespace SimpleBranchCrossingPaths318
open Set Filter
open scoped Topology
open LegendreHalfPlaneAnalyticSheets318

/-- Explicit lifts for a crossing around a simple square branch. Straight
source segments in the first/fourth quadrants square to actual upper/lower
base arcs. No trigonometric conventions or abstract monodromy supplied. -/
@[expose] def rootArc (upper:Bool) (s t:ℝ) : ℂ :=
  ((s*(1-t):ℝ):ℂ)+(if upper then Complex.I else -Complex.I)*((s*t:ℝ):ℂ)
@[expose] def baseArc (a:ℝ) (upper:Bool) (s t:ℝ) : ℂ := (a:ℂ)+rootArc upper s t^2

lemma rootArc_re (upper:Bool) (s t:ℝ) : (rootArc upper s t).re=s*(1-t) := by
  cases upper <;> simp [rootArc]
lemma rootArc_im (upper:Bool) (s t:ℝ) :
    (rootArc upper s t).im=if upper then s*t else -(s*t) := by
  cases upper <;> simp [rootArc]
lemma rootArc_continuous (upper:Bool) (s:ℝ) : Continuous (rootArc upper s) := by
  unfold rootArc
  fun_prop
lemma baseArc_continuous (a:ℝ) (upper:Bool) (s:ℝ) : Continuous (baseArc a upper s) :=
  continuous_const.add ((rootArc_continuous upper s).pow 2)

lemma rootArc_start (upper:Bool) (s:ℝ) : rootArc upper s 0=(s:ℂ) := by
  simp [rootArc]
lemma rootArc_end (upper:Bool) (s:ℝ) :
    rootArc upper s 1=(if upper then Complex.I else -Complex.I)*(s:ℂ) := by
  simp [rootArc]
lemma baseArc_start (a:ℝ) (upper:Bool) (s:ℝ) : baseArc a upper s 0=((a+s^2:ℝ):ℂ) := by
  simp [baseArc,rootArc_start]
lemma baseArc_end (a:ℝ) (upper:Bool) (s:ℝ) : baseArc a upper s 1=((a-s^2:ℝ):ℂ) := by
  cases upper <;> simp [baseArc,rootArc_end,mul_pow,Complex.I_sq]
lemma opposite_endpoints (s:ℝ) : rootArc false s 1= -rootArc true s 1 := by
  simp [rootArc_end]
lemma endpoints_distinct (s:ℝ) (hs:0<s) : rootArc false s 1≠rootArc true s 1 := by
  intro h
  have hh:=congrArg Complex.im h
  simp only [rootArc_im] at hh
  norm_num at hh
  linarith

lemma baseArc_side (a:ℝ) (upper:Bool) (s t:ℝ) :
    side upper (baseArc a upper s t)=2*s^2*t*(1-t) := by
  cases upper <;> simp [side,baseArc,pow_two,Complex.mul_im,rootArc_re,rootArc_im] <;> ring
/-- Every strict interior point lies in the specified ACTUAL halfplane.
At both ends the base is real, and the two lifts have opposite endpoints. -/
lemma interior_halfplane (a:ℝ) (upper:Bool) (s t:ℝ) (hs:0<s) (ht:t∈Ioo 0 1) :
    baseArc a upper s t∈domain upper := by
  change 0<side upper (baseArc a upper s t)
  rw [baseArc_side]
  exact mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hs)) ht.1)
    (sub_pos.mpr ht.2)
lemma rootArc_nonzero (upper:Bool) (s t:ℝ) (hs:0<s) (ht:t∈Icc 0 1) :
    rootArc upper s t≠0 := by
  intro h
  have hr:=congrArg Complex.re h
  have hi:=congrArg Complex.im h
  rw [rootArc_re,Complex.zero_re] at hr
  rw [rootArc_im,Complex.zero_im] at hi
  have hs0:s≠0:=ne_of_gt hs
  have ht0:t=0:=by
    cases upper
    · exact (mul_eq_zero.mp (neg_eq_zero.mp hi)).resolve_left hs0
    · exact (mul_eq_zero.mp hi).resolve_left hs0
  rw [ht0,sub_zero,mul_one] at hr
  exact hs0 hr

/-- Uniform control keeps BOTH complete crossing lifts inside any chosen
actual branch coordinate neighborhood, not just their endpoints. -/
lemma rootArc_norm (upper:Bool) (s t:ℝ) (hs:0≤s) (ht:t∈Icc 0 1) :
    ‖rootArc upper s t‖≤s := by
  have hleft:0≤s*(1-t):=mul_nonneg hs (sub_nonneg.mpr ht.2)
  have hright:0≤s*t:=mul_nonneg hs ht.1
  have hh:=norm_add_le (((s*(1-t):ℝ):ℂ))
    ((if upper then Complex.I else -Complex.I)*((s*t:ℝ):ℂ))
  have hunit:‖(if upper then Complex.I else -Complex.I:ℂ)‖=1:=by
    cases upper <;> simp
  simp only [norm_mul,hunit,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hleft,abs_of_nonneg hright] at hh
  change ‖rootArc upper s t‖≤_ at hh
  have he:s*(1-t)+s*t=s:=by ring
  exact hh.trans_eq he
lemma baseArc_distance (a:ℝ) (upper:Bool) (s t:ℝ) (hs:0≤s) (ht:t∈Icc 0 1) :
    dist (baseArc a upper s t) (a:ℂ)≤s^2 := by
  rw [dist_eq_norm]
  have he:baseArc a upper s t-(a:ℂ)=rootArc upper s t^2:=by dsimp [baseArc];ring
  rw [he,norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (rootArc_norm upper s t hs ht) 2

theorem exists_small_crossing {U:Set ℂ} (hU:U∈𝓝 (0:ℂ)) :
    ∃s:ℝ,0<s ∧ ∀upper t,t∈Icc 0 1 → rootArc upper s t∈U := by
  obtain ⟨ε,hε,hsub⟩:=Metric.mem_nhds_iff.mp hU
  refine ⟨ε/2,by positivity,?_⟩
  intro upper t ht
  apply hsub
  rw [Metric.mem_ball,dist_zero_right]
  exact (rootArc_norm upper (ε/2) t (by positivity) ht).trans_lt (by linarith)
end SimpleBranchCrossingPaths318
