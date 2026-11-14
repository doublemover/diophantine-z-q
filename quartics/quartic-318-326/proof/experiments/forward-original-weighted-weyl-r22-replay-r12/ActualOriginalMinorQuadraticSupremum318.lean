module
public import ActualOriginalUniformLogKernel318
public section
noncomputable section
namespace ActualOriginalMinorQuadraticSupremum318
open ActualOriginalUniformLogKernel318 ActualOriginalQuadraticIntervalKernel318
open ActualOriginalQuadraticFourthMoment318 ActualOriginalCompleteLogKernel318
open ActualOriginalMajorArcDomain318 ActualOriginalMinorDirichlet318

@[expose] def minorQuadraticBudget (c : ℤ) (H N Q : ℕ) : ℝ :=
  uniformLogBudget ((|c| : ℤ)*(H : ℤ) : ℤ) (2*(H : ℝ)+1) N Q

lemma actual_minor_quadratic_budget_nonneg (c : ℤ) (H N Q : ℕ)
    (hN : 0<N) (hQ : 0<Q) : 0≤minorQuadraticBudget c H N Q := by
  apply actual_uniform_log_nonneg
  · exact_mod_cast mul_nonneg (abs_nonneg c) (Int.natCast_nonneg H)
  · positivity
  · exact_mod_cast hN
  · exact_mod_cast (show 1≤Q by omega)

/-- Actual minor points produce their own reduced approximant. The bound
is simultaneous over every consecutive prefix/subinterval of [-H,H]. -/
theorem actual_minor_quadratic_square (c : ℤ) (hc : c≠0) (H N Q : ℕ)
    (hN : 0<N) (hQ : 0<Q) (B : ℝ) (hB : 0<B)
    (hs : ((N : ℝ)+1)^3≤B) (hwidth : 1/((Q : ℝ)+1)<radius N B)
    (lo hi : ℤ) (hlo : -(H : ℤ)≤lo) (hhi : hi≤H)
    (t : ℝ) (ht : t∈minorDomain N B) :
    ‖quadraticSum (Finset.Icc lo hi) c (t : AddCircle (1 : ℝ))‖^2≤
      minorQuadraticBudget c H N Q := by
  obtain ⟨a,q,hNq,hqQ,hcqa,he,he'⟩ := actual_minor_dirichlet N hN B hB hs Q hQ hwidth t ht
  have hq : 0<q := by omega
  have hK : (0 : ℤ)≤|c|*(H : ℤ) := mul_nonneg (abs_nonneg c) (Int.natCast_nonneg H)
  have hb := actual_quadratic_interval_kernel H lo hi c (Int.natCast_nonneg H) hlo hhi hc t
  apply hb.trans
  apply (actual_complete_log_kernel a q (|c|*(H : ℤ)) t (2*(H : ℝ)+1)
    hq hcqa hK he' (by positivity)).trans
  apply actual_log_kernel_uniform
  · exact_mod_cast hK
  · positivity
  · exact_mod_cast hN
  · exact hq
  · exact_mod_cast (le_of_lt hNq)
  · exact_mod_cast hqQ

/-- A genuine uniform pointwise supremum, with no moment/maximal
interchange and no fifth-factor estimate left as a hypothesis. -/
theorem actual_minor_quadratic_supremum (c : ℤ) (hc : c≠0) (H N Q : ℕ)
    (hN : 0<N) (hQ : 0<Q) (B : ℝ) (hB : 0<B)
    (hs : ((N : ℝ)+1)^3≤B) (hwidth : 1/((Q : ℝ)+1)<radius N B)
    (lo hi : ℤ) (hlo : -(H : ℤ)≤lo) (hhi : hi≤H)
    (t : ℝ) (ht : t∈minorDomain N B) :
    ‖quadraticSum (Finset.Icc lo hi) c (t : AddCircle (1 : ℝ))‖≤
      Real.sqrt (minorQuadraticBudget c H N Q) := by
  have hb := actual_minor_quadratic_square c hc H N Q hN hQ B hB hs hwidth lo hi hlo hhi t ht
  have hnon := actual_minor_quadratic_budget_nonneg c H N Q hN hQ
  nlinarith [Real.sq_sqrt hnon,Real.sqrt_nonneg (minorQuadraticBudget c H N Q)]

/-- The order is constructed, not selected by an extra approximation
assumption. No irrationality or unproved denominator distribution. -/
theorem actual_minor_quadratic_canonical (c : ℤ) (hc : c≠0) (H N : ℕ)
    (hN : 0<N) (B : ℝ) (hB : 0<B) (hs : ((N : ℝ)+1)^3≤B)
    (lo hi : ℤ) (hlo : -(H : ℤ)≤lo) (hhi : hi≤H)
    (t : ℝ) (ht : t∈minorDomain N B) :
    ‖quadraticSum (Finset.Icc lo hi) c (t : AddCircle (1 : ℝ))‖≤
      Real.sqrt (minorQuadraticBudget c H N ⌈B^2/(N : ℝ)⌉₊) := by
  obtain ⟨hQ,hw⟩ := actual_minor_dirichlet_order N hN B hB
  exact actual_minor_quadratic_supremum c hc H N _ hN hQ B hB hs hw lo hi hlo hhi t ht

end ActualOriginalMinorQuadraticSupremum318
