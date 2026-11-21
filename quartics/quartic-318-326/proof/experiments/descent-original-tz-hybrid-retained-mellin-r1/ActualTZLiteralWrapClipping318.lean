module
public import Mathlib
public section
noncomputable section
namespace ActualTZLiteralWrapClipping318
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {Z R J : Type*} [Fintype Z] [Fintype R] [Fintype J]

def wrapMass (n : ℕ) (len : Z→R→ℕ) (z : Z) (r : R) : ℝ := (len z r:ℝ)/(n:ℝ)

def kept (n : ℕ) (L : ℝ) (len : Z→R→ℕ)
    (zero : Z→R→J→Prop) (z : Z) (r : R) : ℝ :=
  if (len z r:ℝ)<L ∨ (∃ i,zero z r i) then 0 else wrapMass n len z r

/-- Clipping uses the *actual* normalized original wrap length.
A short positive cell and an exact coincidence are bounded before
selection, and the wrap event never inherits digit independence. -/
theorem lost_mass (n : ℕ) (hn : 0<n) (L : ℝ) (hL : 0≤L)
    (len : Z→R→ℕ) (hlen : ∀ z r,len z r≤n)
    (zero : Z→R→J→Prop) (m : Z→ℝ) (hm : ∀ z,0≤m z) (hm1 : (∑ z : Z,m z)=1)
    (q : ℝ) (hZero : ∀ r i,(∑ z : Z,m z*(if zero z r i then 1 else 0))≤q) :
    (∑ z : Z,m z*(∑ r : R,(wrapMass n len z r-kept n L len zero z r)))≤
      (Fintype.card R:ℝ)*(L/(n:ℝ)+(Fintype.card J:ℝ)*q) := by
  classical
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hPos : 0≤L/(n:ℝ) := div_nonneg hL hn'.le
  have hPoint (z : Z) (r : R) :
      wrapMass n len z r-kept n L len zero z r≤
        L/(n:ℝ)+∑ i : J,if zero z r i then 1 else 0 := by
    have h1 : wrapMass n len z r≤1 :=
      (div_le_one hn').2 (by exact_mod_cast hlen z r)
    have hSum : 0≤∑ i : J,if zero z r i then (1:ℝ) else 0 :=
      Finset.sum_nonneg (fun i _=>by split_ifs <;> norm_num)
    unfold kept
    by_cases hs : (len z r:ℝ)<L
    · rw [if_pos (Or.inl hs),sub_zero]
      exact (div_le_div_of_nonneg_right hs.le hn'.le).trans (le_add_of_nonneg_right hSum)
    · by_cases hz : ∃ i,zero z r i
      · rw [if_pos (Or.inr hz),sub_zero]
        obtain ⟨i,hi⟩ := hz
        have H := Finset.single_le_sum
          (f := fun i : J=>if zero z r i then (1:ℝ) else 0)
          (fun i _=>by split_ifs <;> norm_num) (Finset.mem_univ i)
        rw [if_pos hi] at H
        exact h1.trans (H.trans (le_add_of_nonneg_left hPos))
      · rw [if_neg (fun h=>h.elim hs hz),sub_self]
        exact add_nonneg hPos hSum
  have hCell (r : R) : (∑ z : Z,m z*(wrapMass n len z r-kept n L len zero z r))≤
      L/(n:ℝ)+(Fintype.card J:ℝ)*q := by
    calc
      _ ≤ ∑ z : Z,m z*(L/(n:ℝ)+∑ i : J,if zero z r i then 1 else 0) :=
        Finset.sum_le_sum (fun z _=>mul_le_mul_of_nonneg_left (hPoint z r) (hm z))
      _ = L/(n:ℝ)+(∑ i : J,∑ z : Z,m z*(if zero z r i then 1 else 0)) := by
        simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,hm1,one_mul]
        congr 1
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ _ := by
        apply add_le_add_left
        calc
          _ ≤ ∑ _ : J,q := Finset.sum_le_sum (fun i _=>hZero r i)
          _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _r : R,L/(n:ℝ)+(Fintype.card J:ℝ)*q :=
      Finset.sum_le_sum fun r _=>hCell r
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/-- Uniform weighted effect on a bounded old complex or real
integrand. Its bound is supplied by the original divisor size
majorant, not inferred from length clipping. -/
theorem remove_bounded (n : ℕ) (L : ℝ) (len : Z→R→ℕ)
    (zero : Z→R→J→Prop) (m : Z→ℝ) (hm : ∀ z,0≤m z)
    (f : Z→R→ℂ) (A : ℝ) (hF : ∀ z r,‖f z r‖≤A) :
    ‖∑ z : Z,∑ r : R,((m z*(wrapMass n len z r-kept n L len zero z r):ℝ):ℂ)*f z r‖ ≤
      A*(∑ z : Z,m z*(∑ r : R,(wrapMass n len z r-kept n L len zero z r))) := by
  classical
  have hPos (z : Z) (r : R) : 0≤wrapMass n len z r-kept n L len zero z r := by
    unfold kept wrapMass
    split_ifs <;> positivity
  calc
    _ ≤ ∑ z : Z,∑ r : R,‖((m z*(wrapMass n len z r-kept n L len zero z r):ℝ):ℂ)*f z r‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _=>norm_sum_le _ _))
    _ ≤ ∑ z : Z,∑ r : R,(m z*(wrapMass n len z r-kept n L len zero z r))*A := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hm z) (hPos z r))]
      exact mul_le_mul_of_nonneg_left (hF z r) (mul_nonneg (hm z) (hPos z r))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro r _
      ring

end ActualTZLiteralWrapClipping318
