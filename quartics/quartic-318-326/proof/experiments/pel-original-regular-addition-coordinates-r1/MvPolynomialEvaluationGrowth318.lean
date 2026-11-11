module
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Tactic
public section
noncomputable section
namespace MvPolynomialEvaluationGrowth318
variable {ι : Type*} [Fintype ι]

/-- Polynomial growth in the actual finite product norm. No Euclidean
norm replacement or total-degree estimate is needed. -/
theorem exists_growth (p : MvPolynomial ι ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ v : ι → ℂ,
      ‖MvPolynomial.eval v p‖ ≤ C * (1+‖v‖)^N := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      exact ⟨‖c‖,norm_nonneg _,0,by intro v; simp⟩
  | add p q hp hq =>
      obtain ⟨C,hC,N,hp⟩ := hp
      obtain ⟨D,hD,M,hq⟩ := hq
      refine ⟨C+D,add_nonneg hC hD,N+M,?_⟩
      intro v
      have h1 : 1 ≤ 1+‖v‖ := le_add_of_nonneg_right (norm_nonneg _)
      have hN : (1+‖v‖)^N ≤ (1+‖v‖)^(N+M) := pow_le_pow_right₀ h1 (Nat.le_add_right _ _)
      have hM : (1+‖v‖)^M ≤ (1+‖v‖)^(N+M) := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
      calc
        ‖MvPolynomial.eval v (p+q)‖ ≤ ‖MvPolynomial.eval v p‖ + ‖MvPolynomial.eval v q‖ := by
          rw [MvPolynomial.eval_add]; exact norm_add_le _ _
        _ ≤ C*(1+‖v‖)^N + D*(1+‖v‖)^M := add_le_add (hp v) (hq v)
        _ ≤ C*(1+‖v‖)^(N+M) + D*(1+‖v‖)^(N+M) :=
          add_le_add (mul_le_mul_of_nonneg_left hN hC) (mul_le_mul_of_nonneg_left hM hD)
        _ = (C+D)*(1+‖v‖)^(N+M) := by ring
  | mul_X p i hp =>
      obtain ⟨C,hC,N,hp⟩ := hp
      refine ⟨C,hC,N+1,?_⟩
      intro v
      have hi : ‖v i‖ ≤ 1+‖v‖ := (norm_le_pi_norm v i).trans (le_add_of_nonneg_left zero_le_one)
      calc
        ‖MvPolynomial.eval v (p*MvPolynomial.X i)‖ = ‖MvPolynomial.eval v p‖ * ‖v i‖ := by
          rw [MvPolynomial.eval_mul,MvPolynomial.eval_X,norm_mul]
        _ ≤ (C*(1+‖v‖)^N)*(1+‖v‖) := mul_le_mul (hp v) hi (norm_nonneg _)
          (mul_nonneg hC (pow_nonneg (by positivity) _))
        _ = C*(1+‖v‖)^(N+1) := by rw [pow_succ]; ring

/-- One bound for every member of a specified finite polynomial family,
including the empty family. -/
theorem exists_uniform_growth {J : Type*} (s : Finset J) (p : J → MvPolynomial ι ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ j ∈ s, ∀ v : ι → ℂ,
      ‖MvPolynomial.eval v (p j)‖ ≤ C*(1+‖v‖)^N := by
  classical
  choose C hC N h using fun j => exists_growth (p j)
  let D := ∑ j ∈ s, C j
  let M := s.sup N
  have hD : 0 ≤ D := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨D,hD,M,?_⟩
  intro j hj v
  have hc : C j ≤ D := Finset.single_le_sum (fun i _ => hC i) hj
  have hn : N j ≤ M := Finset.le_sup (f := N) hj
  exact (h j v).trans (mul_le_mul hc
    (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg v)) hn)
    (pow_nonneg (by positivity) _) hD)
end MvPolynomialEvaluationGrowth318
