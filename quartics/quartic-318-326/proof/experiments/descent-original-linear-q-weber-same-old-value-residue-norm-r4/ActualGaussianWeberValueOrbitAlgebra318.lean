module
public import Mathlib.Tactic
public section

namespace ActualGaussianWeberValueOrbitAlgebra318

variable {K : Type*} [Field K]

private theorem eq_or_eq_neg_of_sq {s t : K} (h : s^2 = t^2) : s=t ∨ s= -t := by
  have h0 : (s-t)*(s+t)=0 := by
    calc
      _ = s^2-t^2 := by ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp h0 with hn|hn
  · exact Or.inl (sub_eq_zero.mp hn)
  · apply Or.inr
    linear_combination hn

/-- On the literal model, equal squared abscissae are exactly an
orbit of the four original coordinate turns, even at a degenerate
orbit (where uniqueness of the turn is not asserted). -/
theorem same_value_iff (i : K) (hi : i^2 = -1) (x y u v : K)
    (hP : y^2=x^3-x) (hQ : v^2=u^3-u) :
    u^2=x^2 ↔
      (u=x ∧ v=y) ∨ (u=x ∧ v= -y) ∨
      (u= -x ∧ v=i*y) ∨ (u= -x ∧ v= -(i*y)) := by
  constructor
  · intro h
    rcases eq_or_eq_neg_of_sq h with hu|hu
    · have hv : v^2=y^2 := by rw [hQ,hu,←hP]
      rcases eq_or_eq_neg_of_sq hv with hv|hv
      · exact Or.inl ⟨hu,hv⟩
      · exact Or.inr (Or.inl ⟨hu,hv⟩)
    · have hv : v^2=(i*y)^2 := by
        rw [hQ,hu,mul_pow,hi,hP]
        ring
      rcases eq_or_eq_neg_of_sq hv with hv|hv
      · exact Or.inr (Or.inr (Or.inl ⟨hu,hv⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hu,hv⟩))
  · rintro (⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩) <;> ring

end ActualGaussianWeberValueOrbitAlgebra318
