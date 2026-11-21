module
public import Mathlib
public section
noncomputable section
namespace ActualTZSparseWrapUnion318
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {Z R P : Type*} [Fintype Z] [Fintype R] [Fintype P]

/-- Finite pair union BEFORE any conditioning on the wrap. The
same actual weight θ may depend on the entire independent grid. -/
theorem union_bound (m : Z→ℝ) (θ : Z→R→ℝ)
    (hit : Z→R→Prop) (event : Z→R→P→Prop)
    (hm : ∀ z,0≤m z) (hθ : ∀ z r,0≤θ z r) (hθ1 : ∀ z r,θ z r≤1)
    (hHit : ∀ z r,hit z r→∃ p,event z r p)
    (E : ℝ) (hE : ∀ r p,(∑ z : Z,m z*(if event z r p then 1 else 0))≤E) :
    (∑ z : Z,m z*(∑ r : R,θ z r*(if hit z r then 1 else 0)))≤
      (Fintype.card R:ℝ)*(Fintype.card P:ℝ)*E := by
  classical
  have hBound (z : Z) (r : R) :
      θ z r*(if hit z r then 1 else 0)≤∑ p : P,if event z r p then (1:ℝ) else 0 := by
    by_cases hr : hit z r
    · obtain ⟨p,hp⟩ := hHit z r hr
      rw [if_pos hr,mul_one]
      have h := Finset.single_le_sum (f:=fun p : P=>if event z r p then (1:ℝ) else 0)
        (fun _ _=>by split_ifs <;> norm_num) (Finset.mem_univ p)
      exact (hθ1 z r).trans (by simpa only [if_pos hp] using h)
    · rw [if_neg hr,mul_zero]
      exact Finset.sum_nonneg fun _ _=>by split_ifs <;> norm_num
  calc
    _ ≤ ∑ z : Z,m z*(∑ r : R,∑ p : P,if event z r p then (1:ℝ) else 0) := by
      exact Finset.sum_le_sum (fun z _=>mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun r _=>hBound z r)) (hm z))
    _ = ∑ r : R,∑ p : P,∑ z : Z,m z*(if event z r p then 1 else 0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ ≤ ∑ _r : R,∑ _p : P,E :=
      Finset.sum_le_sum (fun r _=>Finset.sum_le_sum (fun p _=>hE r p))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]

end ActualTZSparseWrapUnion318
