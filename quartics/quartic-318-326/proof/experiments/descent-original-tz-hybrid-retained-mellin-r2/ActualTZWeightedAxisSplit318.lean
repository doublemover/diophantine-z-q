module
public import ActualTZOldProductAverage318
public section
noncomputable section
namespace ActualTZWeightedAxisSplit318
open scoped BigOperators
open ActualTZOldProductAverage318

theorem prob_left {X : Type*} [Fintype X] (a : ℝ) (F : X→ℝ) :
    prob (fun x=>a*F x)=a*prob F := by
  unfold prob
  rw [←Finset.mul_sum,mul_div_assoc]

theorem prob_right {X : Type*} [Fintype X] (a : ℝ) (F : X→ℝ) :
    prob (fun x=>F x*a)=prob F*a := by
  simpa only [mul_comm] using prob_left a F

theorem pair_product {X Y : Type*} [Fintype X] [Fintype Y] (F : X→ℝ) (G : Y→ℝ) :
    prob (fun z : X×Y=>F z.1*G z.2)=prob F*prob G := by
  rw [←nested]
  simp only [prob_left]
  exact prob_right _ _

/-- One weighted Cauchy step with a shared base X. The other
variable alone is copied. Sign of A or B is unrestricted;
the positive face envelope appears once, not squared. -/
theorem split {X T : Type*} [Fintype X] [Fintype T]
    (A U : X→ℝ) (B : X→T→ℝ) (h : ∀ x,|A x|≤U x) :
    |prob (fun x=>A x*prob (B x))|^2≤
      prob U*prob (fun x=>prob (fun t : T×T=>U x*(B x t.1*B x t.2))) := by
  let D (x : X) := prob (B x)
  let Z : ℝ := Fintype.card X
  have hZ : 0≤Z := by unfold Z; positivity
  have hU (x : X) : 0≤U x := (abs_nonneg _).trans (h x)
  have hAbs : |prob (fun x=>A x*D x)|≤prob (fun x=>U x*|D x|) := by
    unfold prob
    rw [abs_div,abs_of_nonneg hZ]
    apply div_le_div_of_nonneg_right _ hZ
    calc
      _ ≤ ∑ x : X,|A x*D x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h x) (abs_nonneg _)
  let P (x : X) := Real.sqrt (U x)
  let Q (x : X) := Real.sqrt (U x)*|D x|
  have hh₁ (x : X) : P x*Q x=U x*|D x| := by
    unfold P Q
    rw [←mul_assoc,←pow_two,Real.sq_sqrt (hU x)]
  have hh₂ (x : X) : (P x)^2=U x := Real.sq_sqrt (hU x)
  have hh₃ (x : X) : (Q x)^2=U x*(D x)^2 := by
    unfold Q
    rw [mul_pow,Real.sq_sqrt (hU x),sq_abs]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ P Q
  simp only [hh₁,hh₂,hh₃] at hCS
  have H : prob (fun x=>U x*|D x|)^2≤prob U*prob (fun x=>U x*(D x)^2) := by
    unfold prob
    rw [div_pow,div_mul_div_comm,←pow_two Z]
    exact div_le_div_of_nonneg_right hCS (sq_nonneg _)
  have hPair (x : X) : prob (fun t : T×T=>U x*(B x t.1*B x t.2))=U x*(D x)^2 := by
    rw [prob_left,pair_product,pow_two] <;> rfl
  simp only [hPair]
  exact (pow_le_pow_left₀ (abs_nonneg _) hAbs 2).trans H

end ActualTZWeightedAxisSplit318
