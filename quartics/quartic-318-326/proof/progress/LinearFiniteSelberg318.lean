module
public import Mathlib.Tactic
public section
noncomputable section

namespace LinearFiniteSelberg318
open scoped BigOperators

/-- Finite Selberg upper majorant on an actual set of rows. A good row has
no nonunit divisor among selected divisors of its integer product. Bad rows
need no sign control on the individual coefficients; the square suffices. -/
theorem upper_majorant {α : Type*} (rows : Finset α) (D : Finset ℕ) (h1 : 1 ∈ D)
    (w : α → ℝ) (hn : ∀ x ∈ rows, 0 ≤ w x) (z : α → ℕ)
    (lam : ℕ → ℝ) (normalized : lam 1=1) (good : α → Prop) [DecidablePred good]
    (sift : ∀ x ∈ rows, good x → ∀ d ∈ D, d ∣ z x → d=1) :
    (∑ x ∈ rows, if good x then w x else 0) ≤
      ∑ x ∈ rows, w x*(∑ d ∈ D, if d ∣ z x then lam d else 0)^2 := by
  classical
  apply Finset.sum_le_sum
  intro x hx
  by_cases h : good x
  · have hv : (∑ d ∈ D, if d ∣ z x then lam d else 0) = 1 := by
      rw [Finset.sum_eq_single 1]
      · simp [normalized]
      · intro d hd hne
        exact ite_eq_right (fun hv => hne (sift x hx h d hd hv))
      · exact fun hn => (hn h1).elim
    simp [h,hv]
  · simp only [ite_eq_right h]
    exact mul_nonneg (hn x hx) (sq_nonneg _)

/-- Divisibility by d,e is exactly divisibility by their lcm; this is the
entry that goes into the evaluated local density of a progression. -/
theorem lcm_indicator (d e N : ℕ) (a b : ℝ) :
    (if d∣N then a else 0)*(if e∣N then b else 0) =
      (if Nat.lcm d e∣N then a*b else 0) := by
  by_cases hd : d∣N <;> by_cases he : e∣N <;> simp [Nat.lcm_dvd_iff,hd,he]

theorem expand_square (D : Finset ℕ) (c : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ D, if d∣N then c d else 0)^2 =
      ∑ d ∈ D, ∑ e ∈ D, (if Nat.lcm d e∣N then c d*c e else 0) := by
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact lcm_indicator d e N (c d) (c e)

def G {ι : Type*} (D : Finset ι) (μ h : ι → ℝ) : ℝ := ∑ d ∈ D, (μ d)^2/h d

/-- Complete the finite Selberg square. Once the divisor quadratic form is
diagonalized, this gives an actual minimizer, not just a Cauchy lower bound.
μ need not be identically ±1; zero squarefree weights are allowed. -/
theorem diagonal_remainder {ι : Type*} (D : Finset ι) (μ h y : ι → ℝ)
    (hh : ∀ d ∈ D, 0 < h d) (hG : 0 < G D μ h)
    (norm : ∑ d ∈ D, μ d*y d = 1) :
    ∑ d ∈ D, h d*(y d-μ d/(h d*G D μ h))^2 =
      (∑ d ∈ D, h d*(y d)^2) - 1/G D μ h := by
  have one (d) (hd : d ∈ D) :
      h d*(y d-μ d/(h d*G D μ h))^2 =
        h d*(y d)^2 - (μ d*y d)*(2/G D μ h) + (μ d^2/h d)*(1/(G D μ h)^2) := by
    field_simp [(hh d hd).ne',hG.ne']
    ring
  rw [Finset.sum_congr rfl one,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,← Finset.sum_mul,norm]
  change _ - 1*(2/G D μ h) + G D μ h*(1/(G D μ h)^2) = _
  field_simp [hG.ne']
  ring

theorem diagonal_optimum {ι : Type*} (D : Finset ι) (μ h : ι → ℝ)
    (hh : ∀ d ∈ D, 0 < h d) (hG : 0 < G D μ h) :
    let y := fun d => μ d/(h d*G D μ h)
    (∑ d ∈ D, μ d*y d) = 1 ∧ (∑ d ∈ D, h d*(y d)^2) = 1/G D μ h ∧
      ∀ v : ι → ℝ, (∑ d ∈ D, μ d*v d)=1 → 1/G D μ h ≤ ∑ d ∈ D, h d*(v d)^2 := by
  dsimp only
  have norm : (∑ d ∈ D, μ d*(μ d/(h d*G D μ h))) = 1 := by
    calc
      _ = ∑ d ∈ D, (μ d^2/h d)*(1/G D μ h) := by
        apply Finset.sum_congr rfl
        intro d hd
        field_simp [(hh d hd).ne',hG.ne']
      _ = 1 := by rw [← Finset.sum_mul]; change G D μ h*(1/G D μ h)=1; field_simp [hG.ne']
  refine ⟨norm,?_,?_⟩
  · have H := diagonal_remainder D μ h _ hh hG norm
    norm_num at H
    rw [one_div]
    exact sub_eq_zero.mp H.symm
  · intro v hv
    have H := diagonal_remainder D μ h v hh hG hv
    have hn : 0 ≤ ∑ d ∈ D, h d*(v d-μ d/(h d*G D μ h))^2 :=
      Finset.sum_nonneg (fun d hd => mul_nonneg (hh d hd).le (sq_nonneg _))
    linarith

end LinearFiniteSelberg318
