module
public import LatticeModelPoint318
public import Mathlib.Analysis.Normed.Module.Connected
public section
noncomputable section
open Filter Set
open scoped Topology
namespace WeierstrassODE318
set_option maxHeartbeats 0

lemma derivative_order (L : PeriodPair) :
    meromorphicOrderAt L.derivWeierstrassP 0 = (-3 : WithTop ℤ) := by
  have h := meromorphicOrderAt_deriv_eq_sub_one (f := L.weierstrassP) (x := 0)
    (n := -2) (by norm_num) (by simpa using L.order_weierstrassP 0 L.lattice.zero_mem)
  simpa using h

lemma derivative_not_identically_zero (L : PeriodPair) :
    ¬ (∀ z ∈ (L.lattice : Set ℂ)ᶜ, L.derivWeierstrassP z = 0) := by
  intro h
  have hz : meromorphicOrderAt L.derivWeierstrassP 0 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz hn
      apply h z
      simp only [mem_compl_iff, Set.mem_sdiff, SetLike.mem_coe, mem_singleton_iff] at hn hz ⊢
      aesop)
  rw [derivative_order] at hz
  norm_num at hz

lemma derivative_factor (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z *
      (deriv L.derivWeierstrassP z - 6 * L.weierstrassP z ^ 2 + L.g₂ / 2) = 0 := by
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hD := (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have he : (fun w => L.derivWeierstrassP w ^ 2) =ᶠ[𝓝 z]
      (fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact L.derivWeierstrassP_sq w hw
  have hleft := hD.pow 2
  have hright := (((hP.pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃
  have hh := hleft.unique (hright.congr_of_eventuallyEq he)
  dsimp at hh
  linear_combination hh / 2

/-- The actual second-order Weierstrass equation, including zeros of the first derivative. -/
theorem second_derivative (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have hc : IsPreconnected ((L.lattice : Set ℂ)ᶜ) :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).isPreconnected
  have ha : AnalyticOnNhd ℂ
      (fun w => deriv L.derivWeierstrassP w - 6 * L.weierstrassP w ^ 2 + L.g₂ / 2)
      (L.lattice : Set ℂ)ᶜ := by
    intro w hw
    have hp := L.analyticOnNhd_weierstrassP w hw
    have hd := (L.analyticOnNhd_derivWeierstrassP w hw).deriv
    fun_prop
  rcases L.analyticOnNhd_derivWeierstrassP.eq_zero_or_eq_zero_of_mul_eq_zero ha
    (fun w hw => derivative_factor L w hw) hc with hzero | hode
  · exact False.elim (derivative_not_identically_zero L hzero)
  · have := hode z hz
    linear_combination this
end WeierstrassODE318
