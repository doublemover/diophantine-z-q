module
public import ActualOriginalQuadraticIntervalKernel318
public section
noncomputable section
namespace ActualOriginalUniformLogKernel318
open ActualOriginalReciprocalLogBudget318 ActualOriginalCompleteLogKernel318
open ActualOriginalCompleteTwoAxisWeyl318

/-- Expanded before replacing q by its upper/lower bounds. This avoids
the false cross-term H*Q/N caused by bounding both unexpanded factors. -/
@[expose] def uniformLogBudget (K L n Q : ℝ) : ℝ :=
  32*K*L/n+32*K*(1+Real.log Q)+4*L+4*Q*(1+Real.log Q)

lemma actual_uniform_log_nonneg (K L n Q : ℝ) (hK : 0≤K) (hL : 0≤L)
    (hn : 0<n) (hQ : 1≤Q) : 0≤uniformLogBudget K L n Q := by
  have hl := Real.log_nonneg hQ
  unfold uniformLogBudget
  positivity

/-- Every reduced denominator in the entire range n<=q<=Q is covered,
with exact cancellation of q in the mixed logarithmic term. -/
theorem actual_log_kernel_uniform (K L n Q : ℝ) (q : ℤ)
    (hK : 0≤K) (hL : 0≤L) (hn : 0<n) (hq : 0<q)
    (hnq : n≤(q : ℝ)) (hqQ : (q : ℝ)≤Q) :
    (16*K/(q : ℝ)+2)*logBlockBudget L q≤uniformLogBudget K L n Q := by
  have hqp : (0 : ℝ)<q := by exact_mod_cast hq
  have hq1 : (1 : ℝ)≤q := by exact_mod_cast (show (1 : ℤ)≤q by omega)
  have hQ : 1≤Q := hq1.trans hqQ
  have hlog : Real.log (q : ℝ)≤Real.log Q := Real.log_le_log hqp hqQ
  have hlQ : 0≤1+Real.log Q := by linarith [Real.log_nonneg hQ]
  have hdiv : 32*K*L/(q : ℝ)≤32*K*L/n := div_le_div_of_nonneg_left (by positivity) hn hnq
  have hterm := mul_le_mul_of_nonneg_left hlog (show 0≤32*K by positivity)
  have hlast : (q : ℝ)*(1+Real.log (q : ℝ))≤Q*(1+Real.log Q) :=
    (mul_le_mul_of_nonneg_left (add_le_add_left hlog 1) (le_of_lt hqp)).trans
      (mul_le_mul_of_nonneg_right hqQ hlQ)
  have he : (16*K/(q : ℝ)+2)*logBlockBudget L q=
      32*K*L/(q : ℝ)+32*K*(1+Real.log (q : ℝ))+4*L+4*(q : ℝ)*(1+Real.log (q : ℝ)) := by
    unfold logBlockBudget
    field_simp [ne_of_gt hqp]
    <;> ring
  rw [he]
  unfold uniformLogBudget
  nlinarith

end ActualOriginalUniformLogKernel318
