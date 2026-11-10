module
public import FiniteGaussianNormCount318
public section
noncomputable section
namespace FiniteNormDifferenceCount318
open FiniteGaussianNormCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def NormDifference (s : F) :=
  {z : (F×F)×(F×F) // z.1.1^2+z.1.2^2-(z.2.1^2+z.2.2^2)=s}

@[expose] def normDifferenceFibers (s : F) :
    NormDifference s ≃ (Σ t : F, NormFiber t × NormFiber (t-s)) where
  toFun z := ⟨z.1.1.1^2+z.1.1.2^2,
    ⟨z.1.1,rfl⟩,⟨z.1.2,by linear_combination -z.2⟩⟩
  invFun z := ⟨(z.2.1.1,z.2.2.1),by linear_combination z.2.1.2-z.2.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by
    rcases z with ⟨t,⟨a,ha⟩,⟨b,hb⟩⟩
    cases ha
    rfl

lemma norm_indicator (hF : ringChar F≠2) (h2 : (2:F)≠0) (t : F) :
    (Nat.card (NormFiber t):ℤ)=(Fintype.card F:ℤ)-quadraticChar F (-1:F)+
      if t=0 then (Fintype.card F:ℤ)*quadraticChar F (-1:F) else 0 := by
  by_cases ht : t=0
  · subst t
    rw [norm_zero hF,if_pos rfl]
    ring
  · rw [norm_nonzero hF h2 t ht,if_neg ht,add_zero]

lemma sum_two_indicators (A B : ℤ) (s : F) :
    (∑ t : F, (A+if t=0 then B else 0)*(A+if t-s=0 then B else 0))=
      (Fintype.card F:ℤ)*A^2+2*A*B+(if s=0 then B^2 else 0) := by
  classical
  have he (t : F) : (A+if t=0 then B else 0)*(A+if t-s=0 then B else 0)=
      A^2+(if t=0 then A*B else 0)+(if t=s then A*B else 0)+
      (if t=0 ∧ t=s then B^2 else 0) := by
    by_cases h0 : t=0 <;> by_cases hs : t=s <;> simp [h0,hs,sub_eq_zero] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib]
  by_cases hs : s=0
  · subst s
    simp only [and_self,if_pos rfl]
    simp
    <;> ring
  · have hz : ∑ t : F, (if t=0 ∧ t=s then B^2 else 0)=0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have he : ¬(t=0 ∧ t=s) := by rintro ⟨h0,h1⟩; exact hs (h1.symm.trans h0)
      rw [if_neg he]
    rw [hz,if_neg hs]
    simp
    <;> ring

/-- Count every literal pair of norm fibers, retaining the zero difference. -/
theorem difference_count (hF : ringChar F≠2) (h2 : (2:F)≠0) (s : F) :
    (Nat.card (NormDifference s):ℤ)=(Fintype.card F:ℤ)^3-(Fintype.card F:ℤ)+
      if s=0 then (Fintype.card F:ℤ)^2 else 0 := by
  classical
  have hc : (Nat.card (NormDifference s):ℤ)=
      ∑ t : F, (Nat.card (NormFiber t):ℤ)*(Nat.card (NormFiber (t-s)):ℤ) := by
    rw [Nat.card_congr (normDifferenceFibers s)]
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod,Nat.cast_sum,Nat.cast_mul]
  rw [hc]
  simp_rw [norm_indicator hF h2]
  rw [sum_two_indicators]
  have he : (quadraticChar F (-1:F))^2=1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have ha : (Fintype.card F:ℤ)*((Fintype.card F:ℤ)-quadraticChar F (-1:F))^2+
      2*((Fintype.card F:ℤ)-quadraticChar F (-1:F))*
        ((Fintype.card F:ℤ)*quadraticChar F (-1:F))=
      (Fintype.card F:ℤ)^3-(Fintype.card F:ℤ) := by
    calc
      _ = (Fintype.card F:ℤ)^3-(Fintype.card F:ℤ)*(quadraticChar F (-1:F))^2 := by ring
      _ = _ := by rw [he,mul_one]
  rw [ha,mul_pow,he,mul_one]

end FiniteNormDifferenceCount318
