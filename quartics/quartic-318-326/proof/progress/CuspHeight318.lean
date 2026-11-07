module
public import CuspFiber318
public import RationalAbsoluteHeight
public section
noncomputable section
namespace CuspHeight318
open NumberField Height
set_option maxHeartbeats 0

theorem rational_absolute_height (q:ℚ) : absLogHeight₁ q=Height.logHeight₁ q := by
  rw [Rat.logHeight₁_eq_log_max]
  simpa using RationalAbsoluteHeight.absLogHeight_ratCast ℚ q

theorem reciprocal_nat_height (n:ℕ) (hn:n≠0) :
    absLogHeight₁ (1/(n:ℚ))=Real.log n := by
  letI : NeZero n := ⟨hn⟩
  rw [rational_absolute_height,one_div,Height.logHeight₁_inv,Rat.logHeight₁_natCast]

/-- The candidate height is the actual absolute logarithmic height. -/
theorem candidate_height (g i:ℕ) (hg:2≤g) (hi:i≤g^3+1) :
    absLogHeight₁ (1/((2:ℚ)^128+i)) ≤ 100+3*Real.log (g+1) := by
  have hn : 2^128+i≠(0:ℕ) := by positivity
  letI : NeZero (2^128+i) := ⟨hn⟩
  rw [rational_absolute_height,one_div,Height.logHeight₁_inv]
  have hid : (2:ℚ)^128+i=((2^128+i:ℕ):ℚ) := by norm_cast
  rw [hid,Rat.logHeight₁_natCast]
  convert CuspFiber318.candidate_log_height g i hg hi using 1 <;> norm_num

end CuspHeight318
#print axioms CuspHeight318.rational_absolute_height
#print axioms CuspHeight318.reciprocal_nat_height
#print axioms CuspHeight318.candidate_height
