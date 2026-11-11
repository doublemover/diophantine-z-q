module
public import FiniteCoefficientVanishing318
public section
noncomputable section
namespace FiniteCoefficientFiberCount318
open FiniteCoefficientVanishing318 FiniteGaussianNormCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fiber_product (hF : ringChar F≠2) (h2 : (2:F)≠0) (κ g w : F)
    (hκ : κ≠0) (hw : w≠0) :
    (Nat.card (NormFiber (-g*w^2)):ℤ)*(Nat.card (NormFiber (-(g+κ)*w^2)):ℤ)=
      if g=0 ∨ g= -κ then
        ((Fintype.card F:ℤ)+((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F))*
          ((Fintype.card F:ℤ)-quadraticChar F (-1:F))
      else ((Fintype.card F:ℤ)-quadraticChar F (-1:F))^2 := by
  by_cases hg : g=0
  · subst g
    rw [if_pos (Or.inl rfl)]
    simp only [neg_zero,zero_mul,zero_add]
    rw [norm_zero hF,norm_nonzero hF h2 _ (mul_ne_zero (neg_ne_zero.mpr hκ) (pow_ne_zero 2 hw))]
  · by_cases hk : g= -κ
    · subst g
      rw [if_pos (Or.inr rfl)]
      simp only [neg_neg,neg_add_cancel,neg_zero,zero_mul]
      rw [norm_nonzero hF h2 _ (mul_ne_zero hκ (pow_ne_zero 2 hw)),norm_zero hF]
      ring
    · rw [if_neg (not_or.mpr ⟨hg,hk⟩)]
      have hgk : g+κ≠0 := by simpa only [ne_eq,add_eq_zero_iff_eq_neg] using hk
      rw [norm_nonzero hF h2 _ (mul_ne_zero (neg_ne_zero.mpr hg) (pow_ne_zero 2 hw)),
        norm_nonzero hF h2 _ (mul_ne_zero (neg_ne_zero.mpr hgk) (pow_ne_zero 2 hw))]
      ring

lemma sum_two_special (i₀ i₁ : ι) (hne : i₀≠i₁) (A B : ℤ) :
    (∑ i : ι, if i=i₀ ∨ i=i₁ then A else B)=
      2*A+((Fintype.card ι:ℤ)-2)*B := by
  classical
  have he (i : ι) : (if i=i₀ ∨ i=i₁ then A else B)=
      B+(if i=i₀ then A-B else 0)+(if i=i₁ then A-B else 0) := by
    by_cases h0 : i=i₀ <;> by_cases h1 : i=i₁
    · exact False.elim (hne (h0.symm.trans h1))
    all_goals simp [h0,h1] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp
  <;> ring

/-- For every nonzero original w, exactly the two distinguished coefficients
have one zero norm target. All other coefficient fibers have two nonzero targets. -/
theorem nonzero_card (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (κ : F) (hκ : κ≠0) (γ : ι → F) (hγ : Function.Injective γ)
    (i₀ i₁ : ι) (h0 : γ i₀=0) (h1 : γ i₁= -κ) (w : F) (hw : w≠0) :
    (Nat.card (Locus κ γ w):ℤ)=
      2*((Fintype.card F:ℤ)+((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F))*
        ((Fintype.card F:ℤ)-quadraticChar F (-1:F))+
      ((Fintype.card ι:ℤ)-2)*((Fintype.card F:ℤ)-quadraticChar F (-1:F))^2 := by
  have hne : i₀≠i₁ := by
    intro he
    have hh : (0:F)= -κ := h0.symm.trans ((congrArg γ he).trans h1)
    exact hκ (neg_eq_zero.mp hh.symm)
  have he0 (i : ι) : γ i=0 ↔ i=i₀ := by rw [←h0]; exact hγ.eq_iff
  have he1 (i : ι) : γ i= -κ ↔ i=i₁ := by rw [←h1]; exact hγ.eq_iff
  rw [locus_card_sum κ γ hγ w hw]
  simp_rw [fiber_product hF h2 κ _ w hκ hw,he0,he1]
  rw [sum_two_special i₀ i₁ hne]
  ring

end FiniteCoefficientFiberCount318
