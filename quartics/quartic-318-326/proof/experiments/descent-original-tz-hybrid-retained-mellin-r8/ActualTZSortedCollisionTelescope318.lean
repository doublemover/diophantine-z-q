module
public import Mathlib
public section
noncomputable section
namespace ActualTZSortedCollisionTelescope318
open scoped BigOperators

/-- Exact exponential telescoping in increasing prime order. It
does not require disjointness or probabilistic independence of any
of the summands. Arbitrary signed real input is allowed here. -/
theorem exp_telescope (S : Finset ℕ) (a : ℕ→ℝ) :
    Real.exp (∑ p∈S,a p)-1 =
      ∑ p∈S,(Real.exp (a p)-1)*Real.exp (∑ q∈S.filter (fun q=>q<p),a q) := by
  classical
  refine Finset.induction_on_max S (by simp) ?_
  intro p T hmax ih
  have hp : p∉T := fun h => (lt_irrefl p) (hmax p h)
  have hfilter : (insert p T).filter (fun q=>q<p)=T := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_insert]
    constructor
    · rintro ⟨rfl|hq,hl⟩
      · exact (lt_irrefl p hl).elim
      · exact hq
    · intro h
      exact ⟨Or.inr h,hmax q h⟩
  have hbelow (q : ℕ) (hq : q∈T) :
      (insert p T).filter (fun z=>z<q)=T.filter (fun z=>z<q) := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_insert]
    constructor
    · rintro ⟨rfl|hz,hl⟩
      · exact (not_lt_of_ge (hmax q hq).le hl).elim
      · exact ⟨hz,hl⟩
    · rintro ⟨hz,hl⟩
      exact ⟨Or.inr hz,hl⟩
  rw [Finset.sum_insert hp,Finset.sum_insert hp,hfilter]
  calc
    _ = (Real.exp (a p)-1)*Real.exp (∑ q∈T,a q)+
        (Real.exp (∑ q∈T,a q)-1) := by rw [Real.exp_add]; ring
    _ = _ := by
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [hbelow q hq]

theorem exp_diff_le (u C : ℝ) (h₀ : 0≤u) (hC : u≤C) :
    Real.exp u-1≤Real.exp C*u := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
  rw [←Real.exp_add,neg_add_cancel,Real.exp_zero] at H
  have A := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hC) h₀
  nlinarith only [H,A]

end ActualTZSortedCollisionTelescope318
