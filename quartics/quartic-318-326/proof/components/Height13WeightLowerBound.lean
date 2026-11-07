module
public import AcyclicWeightLowerBound
public section
namespace Height13WeightLowerBound
open AcyclicWeightLowerBound

/-- After specializing delta=1, the isolated order29 target is e^57. -/
theorem six_helpers_required (xs : List ℤ) (lo hi : ℤ)
    (h : Sequence 0 1 xs lo hi) (target : 57 ∈ xs) : 6 ≤ xs.length := by
  have hw := width 0 1 lo hi xs h
  have he := endpoints 0 1 lo hi xs h
  have ht := contains 0 1 lo hi 57 xs h target
  have hbig : (57:ℤ) ≤ 2^xs.length := by nlinarith
  by_contra hn
  have hn : xs.length ≤ 5 := by omega
  have hp : (2:ℤ)^xs.length ≤ 2^5 := pow_le_pow_right₀ (by norm_num) hn
  norm_num at hp
  omega

/-- The six-helper construction realizes the optimal isolated exponent pattern.
The full detector's exceptional zero branch is a separate arithmetic argument. -/
theorem six_helpers_attained : Sequence 0 1 [2,4,8,15,29,57] 0 57 := by
  refine Sequence.cons (Step.quotient 1 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 2 2 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 4 4 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 8 8 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 15 15 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 29 29 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  convert Sequence.nil 0 57 using 1 <;> norm_num

end Height13WeightLowerBound
