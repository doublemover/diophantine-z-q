module
public import OriginalPeriodInfinityExtension318
public section
noncomputable section
namespace WeierstrassReciprocalPole318
open Complex Filter Topology
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3200000
variable (P : PeriodPair) (a : ℂ)

/-- Reciprocal of the actual omitted-value function, with the genuine
removable value0 at every lattice pole. -/
@[expose] def reciprocal (z : ℂ) : ℂ :=
  if z∈P.lattice then 0 else 1/(P.weierstrassP z-a)
@[expose] def regular (z : ℂ) : ℂ :=
  z^2/(1+z^2*(P.weierstrassPExcept 0 z-a))
lemma reciprocal_zero : reciprocal P a 0=0 := by simp [reciprocal]
lemma regular_zero : regular P a 0=0 := by simp [regular]
lemma regular_analytic : AnalyticAt ℂ (regular P a) 0 := by
  have hA := P.analyticAt_weierstrassPExcept 0
  exact (analyticAt_id.pow 2).div
    (analyticAt_const.add ((analyticAt_id.pow 2).mul (hA.sub analyticAt_const))) (by simp)

lemma regular_denominator (z : ℂ) (hz : z≠0) :
    1+z^2*(P.weierstrassPExcept 0 z-a)=z^2*(P.weierstrassP z-a) := by
  have h := P.weierstrassPExcept_add (0:P.lattice) z
  simp only [Submodule.coe_zero,sub_zero,zero_pow (by decide : (2:ℕ)≠0),div_zero,sub_zero] at h
  rw [←h]
  field_simp [hz]
  ring

/-- The actual reciprocal extends analytically at the lattice origin.
The original missing-value hypothesis is used only off the lattice. -/
theorem reciprocal_analytic_zero
    (hmiss : ∀ z∉P.lattice,P.weierstrassP z≠a) : AnalyticAt ℂ (reciprocal P a) 0 := by
  apply (regular_analytic P a).congr
  filter_upwards [P.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases hz0 : z=0
  · subst z
    rw [regular_zero,reciprocal_zero]
  have hzl : z∉P.lattice := fun h => hz ⟨h,hz0⟩
  have hden : P.weierstrassP z-a≠0 := sub_ne_zero.mpr (hmiss z hzl)
  rw [regular,regular_denominator P a z hz0,reciprocal,if_neg hzl]
  field_simp [hz0,hden]

lemma reciprocal_add_period (z : ℂ) (l : P.lattice) :
    reciprocal P a (z+l.val)=reciprocal P a z := by
  have hm : z+l.val∈P.lattice ↔ z∈P.lattice :=
    P.lattice.toAddSubgroup.add_mem_cancel_right l.property
  simp only [reciprocal,hm,P.weierstrassP_add_coe]
lemma reciprocal_sub_period (z : ℂ) (l : P.lattice) :
    reciprocal P a (z-l.val)=reciprocal P a z := by
  rw [←reciprocal_add_period P a (z-l.val) l,sub_add_cancel]

/-- An omitted finite value would give an ENTIRE periodic reciprocal,
including all original lattice poles, not merely a punctured function. -/
theorem reciprocal_entire
    (hmiss : ∀ z∉P.lattice,P.weierstrassP z≠a) (z : ℂ) :
    AnalyticAt ℂ (reciprocal P a) z := by
  by_cases hz : z∈P.lattice
  · have h0 : AnalyticAt ℂ (reciprocal P a) (z-z) := by
      simpa only [sub_self] using reciprocal_analytic_zero P a hmiss
    have ht : AnalyticAt ℂ (fun w => reciprocal P a (w-z)) z :=
      h0.comp (analyticAt_id.sub analyticAt_const)
    apply ht.congr
    exact Filter.Eventually.of_forall (fun w => reciprocal_sub_period P a w ⟨z,hz⟩)
  · have ha := analyticAt_const.div (P.analyticOnNhd_weierstrassP z hz |>.sub analyticAt_const)
      (sub_ne_zero.mpr (hmiss z hz))
    apply ha.congr
    filter_upwards [P.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    simp only [reciprocal,if_neg hw]
end WeierstrassReciprocalPole318
