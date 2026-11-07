module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
public section
noncomputable section
namespace CuspFiber318
set_option maxHeartbeats 0

/-- More candidate values than bad geometric points gives an entire good fiber,
not merely one good point in a possibly bad fiber. -/
theorem exists_fiber_avoiding {X Y:Type*} [DecidableEq Y]
    (bad:Finset X) (values:Finset Y) (f:X→Y)
    (hcard:bad.card<values.card) :
    ∃a∈values,∀x∈bad,f x≠a := by
  have hcard' : (bad.image f).card<values.card :=
    (Finset.card_image_le).trans_lt hcard
  obtain ⟨a,ha,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
  refine ⟨a,ha,?_⟩
  intro x hx heq
  apply hnot
  rw [←heq]
  exact Finset.mem_image_of_mem f hx

/-- The source's g^3+1 rational choices suffice for the classical bound g^3−g. -/
theorem exists_source_index {X:Type*} (bad:Finset X) (f:X→ℕ)
    (g:ℕ) (hcard:bad.card≤g^3-g) :
    ∃i∈Finset.Icc 1 (g^3+1),∀x∈bad,f x≠i := by
  apply exists_fiber_avoiding bad (Finset.Icc 1 (g^3+1)) f
  rw [Nat.card_Icc]
  omega

/-- Candidate denominators have the actual elementary logarithmic height bound. -/
theorem candidate_log_height (g i:ℕ) (hg:2≤g) (hi:i≤g^3+1) :
    Real.log ((2:ℝ)^128+i) ≤ 100+3*Real.log (g+1) := by
  have hgi : (i:ℝ)≤(g:ℝ)^3+1 := by exact_mod_cast hi
  have hg0 : 0≤(g:ℝ) := by positivity
  have hbase : (1:ℝ)≤2^128 := by norm_num
  have hbound : (2:ℝ)^128+i ≤ 2^128*(g+1)^3 := by
    have hgp : (2:ℝ)≤g := by exact_mod_cast hg
    nlinarith [sq_nonneg (g:ℝ)]
  have hl := Real.log_le_log (show (0:ℝ)<2^128+i by positivity) hbound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
  have htwo := Real.log_two_lt_d9
  norm_num only [Nat.cast_ofNat] at hl
  norm_num only [show (2:ℝ)^128=340282366920938463463374607431768211456 by norm_num]
  linarith

end CuspFiber318
#print axioms CuspFiber318.exists_fiber_avoiding
#print axioms CuspFiber318.exists_source_index
#print axioms CuspFiber318.candidate_log_height
