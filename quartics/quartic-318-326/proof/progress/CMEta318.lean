module
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic
public section
noncomputable section
open Filter Finset
open scoped Topology Real
namespace CMEta318
set_option maxHeartbeats 0

 theorem factor_pos (q:ℂ) (hq:‖q‖<1) (n:ℕ) : 0<‖1-q^(n+1)‖ := by
  have hp:‖q‖^(n+1)<1:=pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hh:=norm_sub_norm_le (1:ℂ) (q^(n+1))
  rw [norm_one,norm_pow] at hh
  linarith

 theorem factor_log_bound (q:ℂ) (hq:‖q‖<1) (n:ℕ) :
    -Real.log ‖1-q^(n+1)‖ ≤ ‖q‖^(n+1)/(1-‖q‖) := by
  have hp0:0≤‖q‖^(n+1):=pow_nonneg (norm_nonneg _) _
  have hpr:‖q‖^(n+1)≤‖q‖:=pow_le_of_le_one (norm_nonneg _) hq.le (by omega)
  have hp:‖q‖^(n+1)<1:=hpr.trans_lt hq
  have hs:0<1-‖q‖^(n+1):=sub_pos.mpr hp
  have hn:1-‖q‖^(n+1)≤‖1-q^(n+1)‖ := by
    simpa only [norm_one,norm_pow] using norm_sub_norm_le (1:ℂ) (q^(n+1))
  have hlog:=Real.log_le_log hs hn
  have hlower:=Real.one_sub_inv_le_log_of_pos hs
  have hrat: (1-‖q‖^(n+1))⁻¹-1=‖q‖^(n+1)/(1-‖q‖^(n+1)) := by
    field_simp
    ring
  have hd:‖q‖^(n+1)/(1-‖q‖^(n+1))≤‖q‖^(n+1)/(1-‖q‖) :=
    div_le_div_of_nonneg_left hp0 (sub_pos.mpr hq) (by linarith)
  linarith

 theorem finite_product_log_bound (q:ℂ) (hq:‖q‖<1) (N:ℕ) :
    -Real.log ‖∏n∈range N,(1-q^(n+1))‖ ≤ ‖q‖/(1-‖q‖)^2 := by
  rw [norm_prod,Real.log_prod (fun n _=>(factor_pos q hq n).ne')]
  rw [←sum_neg_distrib]
  have hsum:=sum_le_sum (s:=range N) (fun n _=>factor_log_bound q hq n)
  apply hsum.trans
  have hs:∑n∈range N,‖q‖^n≤(1-‖q‖)⁻¹ := by
    rw [←tsum_geometric_of_lt_one (norm_nonneg q) hq]
    exact (summable_geometric_of_lt_one (norm_nonneg q) hq).sum_le_tsum _
      (fun n _=>pow_nonneg (norm_nonneg _) _)
  have hm:=mul_le_mul_of_nonneg_left hs (show 0≤‖q‖/(1-‖q‖) by positivity)
  have he:∑n∈range N,‖q‖^(n+1)/(1-‖q‖)=
      (‖q‖/(1-‖q‖))*(∑n∈range N,‖q‖^n) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    rw [pow_succ]
    ring
  rw [he]
  convert hm using 1
  field_simp

/-- The logarithmic estimate on the actual convergent Euler product. -/
theorem tprod_log_bound (q:ℂ) (hq:‖q‖<1) :
    -Real.log ‖∏'n:ℕ,(1-q^(n+1))‖ ≤ ‖q‖/(1-‖q‖)^2 := by
  have hs:Summable (fun n:ℕ=>-q^(n+1)) := by
    apply summable_norm_iff.mp
    simpa only [norm_neg,norm_pow] using
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)
  have hz:(∏'n:ℕ,(1-q^(n+1)))≠0 := by
    simpa only [sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable
      (fun n=>by simpa only [sub_eq_add_neg] using (norm_pos_iff.mp (factor_pos q hq n))) hs.norm
  have ht: Tendsto (fun N:ℕ=>-Real.log ‖∏n∈range N,(1-q^(n+1))‖) atTop
      (𝓝 (-Real.log ‖∏'n:ℕ,(1-q^(n+1))‖)) :=
    ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz)).tendsto.comp
      (ModularForm.multipliable_one_sub_pow hq).hasProd.tendsto_prod_nat.norm).neg
  exact le_of_tendsto' ht (finite_product_log_bound q hq)

theorem eta_log_bound (z:ℂ) (hz:0<z.im) :
    -Real.log (‖ModularForm.eta z‖^2) ≤ Real.pi*z.im/6 +
      2*‖Function.Periodic.qParam 1 z‖/(1-‖Function.Periodic.qParam 1 z‖)^2 := by
  have hq:‖Function.Periodic.qParam 1 z‖<1 :=
    Function.Periodic.norm_qParam_lt_one (by norm_num) hz
  have hb:=tprod_log_bound (Function.Periodic.qParam 1 z) hq
  have hp: (∏'n:ℕ,(1-ModularForm.eta_q n z))≠0 := ModularForm.eta_tprod_ne_zero hz
  have hnorm:‖ModularForm.eta z‖=
      Real.exp (-2*Real.pi*z.im/24)*‖∏'n:ℕ,(1-ModularForm.eta_q n z)‖ := by
    rw [ModularForm.eta,norm_mul,Function.Periodic.norm_qParam]
  rw [Real.log_pow,hnorm,
    Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hp),Real.log_exp]
  change -Real.log ‖∏'n:ℕ,(1-ModularForm.eta_q n z)‖ ≤ _ at hb
  norm_num only [Nat.cast_ofNat]
  linear_combination 2*hb

 theorem reduced_q_bound (z:ℂ) (hy:Real.sqrt 3/2≤z.im) :
    0<z.im ∧ ‖Function.Periodic.qParam 1 z‖<1/16 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hs0:=Real.sqrt_nonneg (3:ℝ)
  have hy0:(1:ℝ)/2≤z.im := by nlinarith
  refine ⟨by linarith,?_⟩
  rw [Function.Periodic.norm_qParam,div_one]
  have he:Real.log ((1:ℝ)/16)=-4*Real.log 2 := by
    rw [one_div,Real.log_inv,show (16:ℝ)=2^4 by norm_num,Real.log_pow]
    norm_num
  rw [←Real.exp_log (by norm_num : (0:ℝ)<1/16),Real.exp_lt_exp,he]
  have hmul:=mul_le_mul_of_nonneg_left hy0 (show 0≤2*Real.pi by positivity)
  nlinarith [Real.pi_gt_three,Real.log_two_lt_d9]

 theorem correction_bound (r:ℝ) (_hr0:0≤r) (hr:r<1/16) :
    2*r/(1-r)^2<32/225 := by
  have hd:0<(1-r)^2:=sq_pos_of_pos (by linarith)
  apply (div_lt_iff₀ hd).mpr
  have hm:=mul_pos (sub_pos.mpr hr) (show 0<16-r by linarith)
  nlinarith

/-- The actual Dedekind eta product estimate at a reduced quadratic period. -/
theorem reduced_eta_bound (z:ℂ) (hy:Real.sqrt 3/2≤z.im) :
    -Real.log (‖ModularForm.eta z‖^2)<Real.pi*z.im/6+32/225 := by
  obtain ⟨hz,hq⟩:=reduced_q_bound z hy
  have he:=eta_log_bound z hz
  have hc:=correction_bound ‖Function.Periodic.qParam 1 z‖ (norm_nonneg _) hq
  linarith

end CMEta318
#print axioms CMEta318.tprod_log_bound

#print axioms CMEta318.reduced_eta_bound
