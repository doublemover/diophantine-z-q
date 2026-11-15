module
public import ActualSelbergDenominator318
public section
noncomputable section
namespace FiniteBooleanMobius318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def zetaEntry (a b : Bool) : ℝ := if a then (if b then 1 else 0) else 1
@[expose] def mobiusEntry (a b : Bool) : ℝ :=
  if a then (if b then 1 else 0) else (if b then -1 else 1)
@[expose] def zeta (a b : ι → Bool) : ℝ := ∏ i,zetaEntry (a i) (b i)
@[expose] def mobius (a b : ι → Bool) : ℝ := ∏ i,mobiusEntry (a i) (b i)
@[expose] def sign (a : ι → Bool) : ℝ := ∏ i,if a i then -1 else 1

lemma one_coordinate_inverse (a c : Bool) :
    (∑ b : Bool,zetaEntry a b*mobiusEntry b c)=if a=c then 1 else 0 := by
  cases a <;> cases c <;> norm_num [zetaEntry,mobiusEntry,Fintype.sum_bool]

lemma product_diagonal (a c : ι → Bool) :
    (∏ i,if a i=c i then (1:ℝ) else 0)=if a=c then 1 else 0 := by
  classical
  by_cases he : a=c
  · subst c
    simp
  · rw [if_neg he]
    have hn : ∃ i,a i≠c i := by
      by_contra h
      apply he
      funext i
      by_contra hi
      exact h ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Exact finite tensor-product Mobius inversion, with no appeal to a
supplied arithmetic inversion formula or an assumed minimizer. -/
lemma matrix_inverse (a c : ι → Bool) :
    (∑ b : ι → Bool,zeta a b*mobius b c)=if a=c then 1 else 0 := by
  classical
  simp only [zeta,mobius,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum]
  simp_rw [one_coordinate_inverse]
  exact product_diagonal a c

@[expose] def inverseTransform (target : (ι → Bool) → ℝ) (a : ι → Bool) : ℝ :=
  ∑ b : ι → Bool,mobius a b*target b

lemma actual_inverse (target : (ι → Bool) → ℝ) (a : ι → Bool) :
    (∑ b : ι → Bool,zeta a b*inverseTransform target b)=target a := by
  classical
  simp only [inverseTransform,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [←mul_assoc,←Finset.sum_mul,matrix_inverse]
  simp

lemma mobius_at_empty (b : ι → Bool) : mobius (fun _ => false) b=sign b := by
  simp only [mobius,sign,mobiusEntry,Bool.false_eq_true,if_false]
lemma sign_sq (b : ι → Bool) : sign b^2=1 := by
  rw [sign,←Finset.prod_pow]
  have hh (i : ι) : (if b i then (-1:ℝ) else 1)^2=1 := by cases b i <;> norm_num
  simp_rw [hh]
  simp
lemma zeta_indicator (a b : ι → Bool) :
    zeta a b=if (∀ i,a i=true → b i=true) then 1 else 0 := by
  classical
  by_cases hh : ∀ i,a i=true → b i=true
  · rw [if_pos hh]
    apply Finset.prod_eq_one
    intro i _
    cases ha : a i
    · simp [zetaEntry,ha]
    · simp [zetaEntry,ha,hh i ha]
  · rw [if_neg hh]
    push_neg at hh
    obtain ⟨i,ha,hb⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [zetaEntry,ha,hb]

lemma mobius_zero_of_not_le (a b : ι → Bool)
    (h : ¬∀ i,a i=true → b i=true) : mobius a b=0 := by
  classical
  push_neg at h
  obtain ⟨i,ha,hb⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [mobiusEntry,ha,hb]

end FiniteBooleanMobius318
