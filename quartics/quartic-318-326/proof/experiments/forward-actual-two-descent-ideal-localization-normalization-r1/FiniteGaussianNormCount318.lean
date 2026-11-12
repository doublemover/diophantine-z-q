module
public import FiniteDifferenceConic318
public section
noncomputable section
namespace FiniteGaussianNormCount318
open FiniteDifferenceConic318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def NormFiber (t : F) := {z : F×F // z.1^2+z.2^2=t}
@[expose] def normFibers (t : F) : NormFiber t ≃ (Σ x : F, {y : F // y^2=t-x^2}) where
  toFun z := ⟨z.1.1,z.1.2,by linear_combination z.2⟩
  invFun z := ⟨(z.1,z.2.1),by linear_combination z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

lemma norm_character_formula (hF : ringChar F≠2) (t : F) :
    (Nat.card (NormFiber t):ℤ)=(Fintype.card F:ℤ)+∑ x : F, quadraticChar F (t-x^2) := by
  classical
  rw [Nat.card_congr (normFibers t)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  have he (x : F) : (Fintype.card {y : F // y^2=t-x^2}:ℤ)=quadraticChar F (t-x^2)+1 := by
    simpa only [Nat.card_eq_fintype_card] using FiniteCurveCharacterCount318.fiber_count hF (t-x^2)
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  ring

lemma square_character_sum : (∑ x : F, quadraticChar F (x^2))=(Fintype.card F:ℤ)-1 := by
  classical
  have he : (∑ x∈(Finset.univ.erase (0:F)),quadraticChar F (x^2))=
      ((Finset.univ.erase (0:F)).card:ℤ) := by
    calc
      _ = ∑ x∈(Finset.univ.erase (0:F)),(1:ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact quadraticChar_sq_one' (Finset.mem_erase.mp hx).1
      _ = _ := by simp
  have hs := Finset.sum_erase_add (Finset.univ:Finset F)
    (fun x : F => quadraticChar F (x^2)) (Finset.mem_univ (0:F))
  rw [he] at hs
  simp only [zero_pow (by decide : (2:ℕ)≠0),map_zero,add_zero,
    Finset.card_erase_of_mem (Finset.mem_univ (0:F)),Finset.card_univ] at hs
  rw [←hs,Nat.cast_sub (Nat.le_of_lt Fintype.one_lt_card),Nat.cast_one]

/-- Literal norm representations of zero, valid in both split and inert
odd-characteristic cases, including the origin. -/
theorem norm_zero (hF : ringChar F≠2) :
    (Nat.card (NormFiber (0:F)):ℤ)=(Fintype.card F:ℤ)+
      ((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F) := by
  rw [norm_character_formula hF]
  have hs : (∑ x : F, quadraticChar F (0-x^2))=
      quadraticChar F (-1:F)*(∑ x : F,quadraticChar F (x^2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show (0:F)-x^2=(-1:F)*x^2 by ring,map_mul]
  rw [hs,square_character_sum]
  ring

/-- Every nonzero norm has exactly q−chi(−1) literal representations.
This establishes the actual first local-sieve fiber input. -/
theorem norm_nonzero (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (t : F) (ht : t≠0) :
    (Nat.card (NormFiber t):ℤ)=(Fintype.card F:ℤ)-quadraticChar F (-1:F) := by
  rw [norm_character_formula hF]
  have hs : (∑ x : F, quadraticChar F (t-x^2))=
      quadraticChar F (-1:F)*(∑ x : F,quadraticChar F (x^2-t)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show t-x^2=(-1:F)*(x^2-t) by ring,map_mul]
  rw [hs,difference_character_sum hF h2 t ht]
  ring

end FiniteGaussianNormCount318
