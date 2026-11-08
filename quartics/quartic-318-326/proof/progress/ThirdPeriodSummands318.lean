module
public import UniformPeriodBounds318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ThirdPeriodSummands318
open UniformPeriodBounds318 PeriodEisenstein318
set_option maxHeartbeats 0

@[expose] def summand (v : Fin 2 → ℤ) (z : ℂ) : ℂ :=
  if v=0 then 0 else 1/((1/3:ℂ)-period v z)^2-1/(period v z)^2

lemma period_ne_third (tau : UpperHalfPlane) (v : Fin 2 → ℤ) :
    period v (tau:ℂ)≠(1/3:ℂ) := by
  intro he
  have hi := congrArg Complex.im he
  rw [period_im] at hi
  norm_num at hi
  have hmz : v 0=0 := hi.resolve_right tau.im_pos.ne'
  have hn : (v 1:ℂ)=(1/3:ℂ) := by simpa [period,hmz] using he
  have h3 : (3:ℂ)*(v 1:ℂ)=1 := by rw [hn]; norm_num
  have h3z : (3:ℤ)*v 1=1 := by exact_mod_cast h3
  omega

lemma summand_analyticAt (tau : UpperHalfPlane) (v : Fin 2 → ℤ) :
    AnalyticAt ℂ (summand v) (tau:ℂ) := by
  change AnalyticAt ℂ (fun z => if v=0 then 0 else 1/((1/3:ℂ)-period v z)^2-1/(period v z)^2) (tau:ℂ)
  by_cases hv : v=0
  · simp only [hv,ite_true]
    exact analyticAt_const
  · have hp : AnalyticAt ℂ (period v) (tau:ℂ) := by unfold period; fun_prop
    have hn := period_ne_zero tau hv
    have hs : (1/3:ℂ)-period v (tau:ℂ)≠0 := sub_ne_zero.mpr (period_ne_third tau v).symm
    simp only [hv,ite_false]
    exact (analyticAt_const.div ((analyticAt_const.sub hp).pow 2) (pow_ne_zero 2 hs)).sub
      (analyticAt_const.div (hp.pow 2) (pow_ne_zero 2 hn))

/-- A single summable lattice majorant controls every sufficiently large period,
uniformly throughout a fixed neighborhood of the period parameter. -/
theorem uniform_bound (tau : UpperHalfPlane) (v : Fin 2 → ℤ) (z : ℂ)
    (hz : ‖z-(tau:ℂ)‖≤tau.im/2) (hv : 4≤‖period v (tau:ℂ)‖) :
    ‖summand v z‖≤80*‖period v (tau:ℂ)‖^(-3:ℝ) := by
  by_cases hv0 : v=0
  · subst v
    norm_num [period] at hv
  · have hlo := (period_bounds tau v z hz).1
    have hb := PeriodPair.weierstrassP_bound 1 (by norm_num) (1/3:ℂ)
      (by norm_num) (period v z) (by linarith)
    have hr := Real.rpow_le_rpow_of_nonpos (by linarith : 0<‖period v (tau:ℂ)‖/2)
      hlo (by norm_num : (-3:ℝ)≤0)
    have hs : (‖period v (tau:ℂ)‖/2)^(-3:ℝ)=8*‖period v (tau:ℂ)‖^(-3:ℝ) := by
      rw [Real.rpow_neg (by positivity),Real.rpow_neg (norm_nonneg _)]
      simp only [Real.rpow_ofNat]
      field_simp
      <;> ring
    rw [hs] at hr
    simp only [summand,hv0,if_false] at ⊢
    norm_num only [mul_one] at hb
    linarith

lemma majorant_summable (tau : UpperHalfPlane) :
    Summable (fun v : Fin 2 → ℤ => 80*‖period v (tau:ℂ)‖^(-3:ℝ)) := by
  have hs : Summable (fun l : (periods tau).lattice => ‖(l:ℂ)‖^(-3:ℝ)) :=
    ZLattice.summable_norm_rpow _ _ (by simp; norm_num)
  have he := (latticeEquiv tau).summable_iff.mpr hs
  exact he.mul_left 80

end ThirdPeriodSummands318
