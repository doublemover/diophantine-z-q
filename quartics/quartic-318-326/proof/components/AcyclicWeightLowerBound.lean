module
public import QuarticOptimization
public section
namespace AcyclicWeightLowerBound

/-- One newly determined monomial coordinate. Constants and existing inputs are
covered by choosing exponent0 among the prerequisites. This is deliberately a
restricted interface, not the full detector or an arbitrary Diophantine system. -/
inductive Step (lo hi x : ℤ) : Prop
  | quotient (a b c : ℤ) (ha : lo ≤ a ∧ a ≤ hi)
      (hb : lo ≤ b ∧ b ≤ hi) (hc : lo ≤ c ∧ c ≤ hi)
      (hx : x=a+b-c) : Step lo hi x
  | squareRoot (a b : ℤ) (ha : lo ≤ a ∧ a ≤ hi)
      (hb : lo ≤ b ∧ b ≤ hi) (hx : 2*x=a+b) : Step lo hi x

theorem step_width (lo hi x : ℤ) (h : Step lo hi x) :
    max hi x-min lo x ≤ 2*(hi-lo) := by
  cases h with
  | quotient a b c ha hb hc hx => omega
  | squareRoot a b ha hb hx => omega

inductive Sequence : ℤ → ℤ → List ℤ → ℤ → ℤ → Prop
  | nil (lo hi : ℤ) : Sequence lo hi [] lo hi
  | cons {lo hi x lo' hi' : ℤ} {xs : List ℤ}
      (head : Step lo hi x) (tail : Sequence (min lo x) (max hi x) xs lo' hi') :
      Sequence lo hi (x::xs) lo' hi'

theorem width (lo hi finalLo finalHi : ℤ) (xs : List ℤ)
    (h : Sequence lo hi xs finalLo finalHi) :
    finalHi-finalLo ≤ (2:ℤ)^xs.length*(hi-lo) := by
  induction h with
  | nil lo hi => simp
  | @cons lo hi x lo' hi' xs hh ht ih =>
    have hs := step_width lo hi x hh
    have hp : 0 ≤ (2:ℤ)^xs.length := by positivity
    have hm := mul_le_mul_of_nonneg_left hs hp
    calc
      hi'-lo' ≤ 2^xs.length*(max hi x-min lo x) := ih
      _ ≤ 2^xs.length*(2*(hi-lo)) := hm
      _ = 2^(x::xs).length*(hi-lo) := by simp [pow_succ]; ring

theorem endpoints (lo hi finalLo finalHi : ℤ) (xs : List ℤ)
    (h : Sequence lo hi xs finalLo finalHi) : finalLo ≤ lo ∧ hi ≤ finalHi := by
  induction h with
  | nil lo hi => exact ⟨le_rfl,le_rfl⟩
  | @cons lo hi x lo' hi' xs hh ht ih =>
    exact ⟨le_trans ih.1 (min_le_left _ _), le_trans (le_max_left _ _) ih.2⟩

theorem contains (lo hi finalLo finalHi x : ℤ) (xs : List ℤ)
    (h : Sequence lo hi xs finalLo finalHi) (hx : x ∈ xs) :
    finalLo ≤ x ∧ x ≤ finalHi := by
  induction h with
  | nil lo hi => simp at hx
  | @cons lo hi y lo' hi' ys hh ht ih =>
    rcases List.mem_cons.mp hx with hxy | hxy
    · subst x
      have he := endpoints _ _ _ _ _ ht
      exact ⟨le_trans he.1 (min_le_right _ _),le_trans (le_max_right _ _) he.2⟩
    · exact ih hxy

theorem seven_helpers_for_exponent81 (xs : List ℤ) (lo hi : ℤ)
    (h : Sequence 0 1 xs lo hi) (target : 81 ∈ xs) : 7 ≤ xs.length := by
  have hw := width 0 1 lo hi xs h
  have he := endpoints 0 1 lo hi xs h
  have ht := contains 0 1 lo hi 81 xs h target
  have hbig : (81:ℤ) ≤ 2^xs.length := by nlinarith
  by_contra hn
  have hsmall : xs.length ≤ 6 := by omega
  have hp : (2:ℤ)^xs.length ≤ 2^6 := pow_le_pow_right₀ (by norm_num) hsmall
  norm_num at hp
  omega


/-- The exponent pattern of the seven-helper construction attains the bound.
This certifies the isolated monomial-step model, not the full arithmetic source. -/
theorem seven_helpers_attained :
    Sequence 0 1 [-1,3,7,-7,21,41,81] (-7) 81 := by
  refine Sequence.cons (Step.quotient 0 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 1 1 (-1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 3 3 (-1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 0 0 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 7 7 (-7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 21 21 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  refine Sequence.cons (Step.quotient 41 41 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) ?_
  convert Sequence.nil (-7) 81 using 1 <;> norm_num

end AcyclicWeightLowerBound
