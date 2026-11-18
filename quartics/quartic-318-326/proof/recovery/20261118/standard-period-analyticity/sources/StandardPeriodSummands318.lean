module
public import ThirdPeriodSummands318
public import EllipticTorsion318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace StandardPeriodSummands318
open UniformPeriodBounds318 PeriodEisenstein318
set_option maxHeartbeats 0

variable (N:ℕ) [NeZero N]
@[expose] def summand (v : Fin 2 → ℤ) (z : ℂ) : ℂ :=
  if v=0 then 0 else 1/((1/(N:ℂ))-period v z)^2-1/(period v z)^2

lemma period_ne_mark (tau : UpperHalfPlane) (hN:1<N) (v : Fin 2 → ℤ) :
    period v (tau:ℂ)≠(1/(N:ℂ)) := by
  intro he
  have hz : ((0:ℂ)*tau+1)/(N:ℂ)∈(periods tau).lattice := by
    simpa [←he,period,latticeMap] using (latticeMap tau v).property
  have hd := ((EllipticTorsion318.divided_period_mem_iff tau N 0 1).mp (by simpa using hz)).2
  have hn : N ∣ 1 := by exact_mod_cast hd
  have := Nat.eq_one_of_dvd_one hn
  omega

lemma summand_analyticAt (hN:1<N) (tau : UpperHalfPlane) (v : Fin 2 → ℤ) :
    AnalyticAt ℂ (summand N v) (tau:ℂ) := by
  change AnalyticAt ℂ (fun z => if v=0 then 0 else 1/((1/(N:ℂ))-period v z)^2-1/(period v z)^2) (tau:ℂ)
  by_cases hv : v=0
  · simp only [hv,ite_true]
    exact analyticAt_const
  · have hp : AnalyticAt ℂ (period v) (tau:ℂ) := by unfold period; fun_prop
    have hn := period_ne_zero tau hv
    have hs : (1/(N:ℂ))-period v (tau:ℂ)≠0 := sub_ne_zero.mpr (period_ne_mark N tau hN v).symm
    simp only [hv,ite_false]
    exact (analyticAt_const.div ((analyticAt_const.sub hp).pow 2) (pow_ne_zero 2 hs)).sub
      (analyticAt_const.div (hp.pow 2) (pow_ne_zero 2 hn))

/-- A single summable lattice majorant controls every sufficiently large period,
uniformly throughout a fixed neighborhood of the period parameter. -/
theorem uniform_bound (hN:1<N) (tau : UpperHalfPlane) (v : Fin 2 → ℤ) (z : ℂ)
    (hz : ‖z-(tau:ℂ)‖≤tau.im/2) (hv : 4≤‖period v (tau:ℂ)‖) :
    ‖summand N v z‖≤80*‖period v (tau:ℂ)‖^(-3:ℝ) := by
  by_cases hv0 : v=0
  · subst v
    norm_num [period] at hv
  · have hlo := (period_bounds tau v z hz).1
    have hN' : (1:ℝ) < N := by exact_mod_cast hN
    have hδ : ‖(1/(N:ℂ))‖ < 1 := by
      rw [norm_div,norm_one,Complex.norm_natCast]
      exact (div_lt_one (by positivity)).mpr hN'
    have hb := PeriodPair.weierstrassP_bound 1 (by norm_num) (1/(N:ℂ))
      hδ (period v z) (by linarith)
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

end StandardPeriodSummands318
