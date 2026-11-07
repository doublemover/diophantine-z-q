module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Tactic
public section
namespace WronskianFinite318
noncomputable section
set_option maxHeartbeats 0

/-- The actual coordinate Wronskian with Javanpeykar's factorial convention. -/
@[expose] def wronskian (g:ℕ) (f:Fin g→ℂ→ℂ) (b:ℂ) : ℂ :=
  Matrix.det (fun i j:Fin g=>iteratedDeriv j.val (f i) b/(j.val.factorial:ℂ))

/-- A direct Leibniz bound suffices; no determinant-size assumption is supplied. -/
theorem norm_det_le (g:ℕ) (M:Matrix (Fin g) (Fin g) ℂ) (B:ℝ) (hB:0≤B)
    (hM:∀i j,‖M i j‖≤B) : ‖M.det‖≤(g.factorial:ℝ)*B^g := by
  rw [Matrix.det_apply]
  apply le_trans (norm_sum_le _ _)
  have he:∀σ:Equiv.Perm (Fin g),‖Equiv.Perm.sign σ • ∏i,M (σ i) i‖≤B^g := by
    intro σ
    rw [Units.smul_def,zsmul_eq_mul,norm_mul,norm_prod]
    have hs:‖(Equiv.Perm.sign σ:ℂ)‖=1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;> simp [h]
    rw [hs,one_mul]
    have hh:=Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _=>norm_nonneg (M (σ i) i)) (fun i _=>hM (σ i) i)
    simpa using hh
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun σ _=>he σ)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul] using hh

/-- The generous manuscript logarithmic bound follows from the actual matrix
entries. The elementary finite determinant proof does not require Hadamard. -/
theorem logarithmic_det_bound (g:ℕ) (hg:1≤g) (N:ℝ) (hN:1≤N)
    (M:Matrix (Fin g) (Fin g) ℂ)
    (hM:∀i j,‖M i j‖≤(g:ℝ)*(Real.exp 21*N)^g) :
    Real.log ‖M.det‖≤100*(g:ℝ)^2*Real.log (2*g*N) := by
  have hgR:(1:ℝ)≤g:=by exact_mod_cast hg
  have hgp:0<(g:ℝ):=by linarith
  have hNp:0<N:=by linarith
  have hbase:2≤(2:ℝ)*g*N := by nlinarith [mul_le_mul_of_nonneg_left hN hgp.le]
  have hbpos:0<(2:ℝ)*g*N:=by linarith
  have hL:(1:ℝ)/2≤Real.log (2*g*N) := by
    have hlog:=Real.log_le_log (by norm_num : (0:ℝ)<2) hbase
    have htwo:=Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at htwo
    linarith
  have hLn:0≤Real.log (2*g*N):=by linarith
  have hLg:Real.log (g:ℝ)≤Real.log (2*g*N) :=
    Real.log_le_log hgp (by nlinarith [mul_le_mul_of_nonneg_left hN hgp.le])
  have hLN:Real.log N≤Real.log (2*g*N) :=
    Real.log_le_log hNp (by nlinarith)
  by_cases hz:M.det=0
  · rw [hz,norm_zero,Real.log_zero]
    positivity
  have hbp:0<(g:ℝ)*(Real.exp 21*N)^g:=by positivity
  have hd:=Real.log_le_log (norm_pos_iff.mpr hz)
    (norm_det_le g M _ hbp.le hM)
  have hfp:0<(g.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos g
  rw [Real.log_mul hfp.ne' (pow_pos hbp g).ne',Real.log_pow,
    Real.log_mul hgp.ne' (pow_pos (mul_pos (Real.exp_pos _) hNp) g).ne',
    Real.log_pow,Real.log_mul (Real.exp_ne_zero _) hNp.ne',Real.log_exp] at hd
  have hf:Real.log (g.factorial:ℝ)≤(g:ℝ)*Real.log (g:ℝ) := by
    have hh:=Real.log_le_log hfp (show (g.factorial:ℝ)≤(g:ℝ)^g by exact_mod_cast Nat.factorial_le_pow g)
    simpa only [Real.log_pow] using hh
  have h1:=mul_le_mul_of_nonneg_left hLg (show 0≤2*(g:ℝ) by positivity)
  have h2:=mul_le_mul_of_nonneg_left hLN (sq_nonneg (g:ℝ))
  have h3:=mul_le_mul_of_nonneg_right (show 2*(g:ℝ)≤2*(g:ℝ)^2 by nlinarith) hLn
  have h4:=mul_le_mul_of_nonneg_left hL (show 0≤42*(g:ℝ)^2 by positivity)
  nlinarith [mul_nonneg (sq_nonneg (g:ℝ)) hLn]

end
end WronskianFinite318
#print axioms WronskianFinite318.norm_det_le
#print axioms WronskianFinite318.logarithmic_det_bound
