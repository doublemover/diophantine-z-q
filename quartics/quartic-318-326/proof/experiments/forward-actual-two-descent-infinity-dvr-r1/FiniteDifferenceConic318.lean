module
public import CanonicalJacobiNorm318
public section
noncomputable section
namespace FiniteDifferenceConic318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def Hyperbola (t : F) := {z : F×F // z.1*z.2=t}
@[expose] def Difference (t : F) := {z : F×F // z.1^2-z.2^2=t}

lemma first_ne (t : F) (ht : t≠0) (z : Hyperbola t) : z.1.1≠0 := by
  intro he
  apply ht
  rw [←z.2,he,zero_mul]

@[expose] def hyperbolaUnits (t : F) (ht : t≠0) : Hyperbola t ≃ Fˣ where
  toFun z := Units.mk0 z.1.1 (first_ne t ht z)
  invFun u := ⟨((u:F),t*(u:F)⁻¹),by
    calc
      _ = t*((u:F)*(u:F)⁻¹) := by ring
      _ = t := by rw [mul_inv_cancel₀ (Units.ne_zero u),mul_one]⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change t*z.1.1⁻¹=z.1.2
      rw [←z.2]
      field_simp [first_ne t ht z]
  right_inv u := by apply Units.ext; rfl

/-- Exact change from the difference conic to a nonzero product fiber. -/
@[expose] def differenceHyperbola (h2 : (2:F)≠0) (t : F) : Difference t ≃ Hyperbola t where
  toFun z := ⟨(z.1.1-z.1.2,z.1.1+z.1.2),by linear_combination z.2⟩
  invFun z := ⟨((z.1.1+z.1.2)/2,(z.1.2-z.1.1)/2),by
    calc
      _ = z.1.1*z.1.2 := by field_simp [h2] <;> ring
      _ = t := z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp [h2] <;> ring
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp [h2] <;> ring

@[expose] def differenceFibers (t : F) : Difference t ≃ (Σ x : F, {y : F // y^2=x^2-t}) where
  toFun z := ⟨z.1.1,z.1.2,by linear_combination -z.2⟩
  invFun z := ⟨(z.1,z.2.1),by linear_combination -z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

/-- Count all solutions of x²−y²=t, including every ordinate fiber. -/
theorem difference_card (h2 : (2:F)≠0) (t : F) (ht : t≠0) :
    Nat.card (Difference t)=Fintype.card F-1 := by
  rw [Nat.card_congr ((differenceHyperbola h2 t).trans (hyperbolaUnits t ht))]
  simp only [Nat.card_eq_fintype_card,Fintype.card_units]

/-- The quadratic polynomial character sum is derived by counting the
same conic two ways, not imported as an assumed local-density formula. -/
theorem difference_character_sum (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (t : F) (ht : t≠0) : (∑ x : F, quadraticChar F (x^2-t))= -1 := by
  classical
  have hf : (Nat.card (Difference t):ℤ)=(Fintype.card F:ℤ)+
      ∑ x : F, quadraticChar F (x^2-t) := by
    rw [Nat.card_congr (differenceFibers t)]
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
    have he (x : F) : (Fintype.card {y : F // y^2=x^2-t}:ℤ)=quadraticChar F (x^2-t)+1 := by
      simpa only [Nat.card_eq_fintype_card] using FiniteCurveCharacterCount318.fiber_count hF (x^2-t)
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    ring
  have hd : (Nat.card (Difference t):ℤ)=(Fintype.card F:ℤ)-1 := by
    rw [difference_card h2 t ht,Nat.cast_sub (Nat.le_of_lt Fintype.one_lt_card),Nat.cast_one]
  omega

end FiniteDifferenceConic318
