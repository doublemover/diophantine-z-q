module
public import CuspCauchy318
public section
noncomputable section
namespace CuspWidthDerivative318
set_option maxHeartbeats 0

/-- The coordinate differential estimate keeps the actual power-map derivative.
The only analytic inputs are the regular qj function's holomorphy, its outer
majorant, and its constant term. -/
theorem actual_width_differential (G:ℂ→ℂ)
    (hhol:∀z,‖z‖≤(1:ℝ)/100 → DifferentiableAt ℂ G z)
    (hbound:∀z,‖z‖≤(1:ℝ)/100 → ‖G z‖≤128)
    (hzero:G 0=1) (m:ℕ) (hm:1≤m) (q_c:ℂ) (hc:q_c≠0)
    (hc1:‖q_c‖≤1) (hsmall:‖q_c^m‖≤Real.exp (-20*Real.pi))
    (M:ℝ) (hM:0<M) (hvalue:G (q_c^m)=q_c^m*(1728*(M:ℂ))) :
    -Real.log ‖deriv (fun z:ℂ=>1728*z^m/G (z^m)) q_c‖ ≤ Real.log M+9 := by
  let B : ℂ→ℂ := fun z=>1728*z/G z
  have hq : q_c^m≠0 := pow_ne_zero _ hc
  have hqsmall : ‖q_c^m‖≤(1:ℝ)/100 := by
    linarith [hsmall.trans_lt CuspDerivative318.tiny_q]
  obtain ⟨he1,he2⟩ := CuspCauchy318.cusp_errors G hhol hbound hzero (q_c^m) hsmall
  have hG : G (q_c^m)≠0 := by
    intro hz
    rw [hz,zero_sub,norm_neg,norm_one] at he1
    norm_num at he1
  have hBd : DifferentiableAt ℂ B (q_c^m) :=
    ((differentiableAt_id.const_mul (1728:ℂ)).div (hhol _ hqsmall) hG)
  have hpow := hasDerivAt_pow m q_c
  have hcomp := hBd.hasDerivAt.comp q_c hpow
  have hder : deriv (fun z:ℂ=>1728*z^m/G (z^m)) q_c =
      deriv B (q_c^m)*((m:ℂ)*q_c^(m-1)) := by
    exact hcomp.deriv
  have hBnorm : (128:ℝ)≤‖deriv B (q_c^m)‖ :=
    CuspCauchy318.actual_belyi_derivative G hhol hbound hzero _ hsmall
  have hlower : ‖q_c^m‖≤‖deriv (fun z:ℂ=>1728*z^m/G (z^m)) q_c‖ := by
    rw [hder,norm_mul,norm_mul,norm_pow,norm_pow,Complex.norm_natCast]
    have hh := CuspDerivative318.chain_factor_lower ‖q_c‖ ‖deriv B (q_c^m)‖ m hm
      (norm_pos_iff.mpr hc) hc1 hBnorm
    nlinarith
  have hinv := CuspDerivative318.inverse_q_bound (q_c^m) (1728*(M:ℂ))
    (G (q_c^m)) hq hvalue he1.le
  have hJ : ‖(1728:ℂ)*(M:ℂ)‖=1728*M := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
    norm_num
  rw [hJ] at hinv
  exact CuspDerivative318.log_differential_bound _ _ M
    ((norm_pos_iff.mpr hq).trans_le hlower) (norm_pos_iff.mpr hq) hM hlower hinv

end CuspWidthDerivative318
#print axioms CuspWidthDerivative318.actual_width_differential
