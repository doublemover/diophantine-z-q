module
public import WeierstrassLaurentModel318

public section
noncomputable section
namespace WeierstrassLaurentFiltration318
open WeierstrassLaurentModel318
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B : ℚ)

/-- Finite-chart monomials have total exponent at most zero in x and z. -/
@[expose] def finiteSpace : Submodule ℚ (Model A B) :=
  Submodule.span ℚ {a | ∃ n : ℤ, ∃ i : Fin 3, n + (i:ℕ) ≤ 0 ∧ a = monomial A B n i}

/-- Infinity-chart monomials have nonnegative powers of z. -/
@[expose] def infinitySpace : Submodule ℚ (Model A B) :=
  Submodule.span ℚ {a | ∃ n : ℤ, ∃ i : Fin 3, 0 ≤ n ∧ a = monomial A B n i}

theorem monomial_mem_finite (n : ℤ) (i : Fin 3) (h : n + (i:ℕ) ≤ 0) :
    monomial A B n i ∈ finiteSpace A B := Submodule.subset_span ⟨n,i,h,rfl⟩
theorem monomial_mem_infinity (n : ℤ) (i : Fin 3) (h : 0 ≤ n) :
    monomial A B n i ∈ infinitySpace A B := Submodule.subset_span ⟨n,i,h,rfl⟩

theorem monomial_shift (n m : ℤ) (i : Fin 3) :
    monomial A B n i * zpow A B m = monomial A B (n+m) i := by
  unfold monomial
  rw [← zpow_mul]
  ring

theorem monomial_x_zero (n : ℤ) : monomial A B n 0 * x A B = monomial A B n 1 := by
  simp only [monomial,pow_zero,pow_one,mul_one]
theorem monomial_x_one (n : ℤ) : monomial A B n 1 * x A B = monomial A B n 2 := by
  simp only [monomial,pow_one,pow_two,mul_assoc]

theorem monomial_x_two (n : ℤ) : monomial A B n 2 * x A B =
    monomial A B (n+1) 0 - A • monomial A B (n+2) 1 - B • monomial A B (n+3) 0 := by
  have h := congrArg (fun a : Model A B => zpow A B n * a) (relation A B)
  simp only [monomial,pow_zero,pow_one,mul_one,Algebra.smul_def,← zpow_mul] at *
  linear_combination h

/-- The actual cubic reduction preserves the finite-chart exponent bound. -/
theorem finite_generator_x (n : ℤ) (i : Fin 3) (h : n + (i:ℕ) ≤ 0) :
    monomial A B n i * (x A B * zpow A B (-1)) ∈ finiteSpace A B := by
  have he : monomial A B n i * (x A B * zpow A B (-1)) =
      monomial A B (n-1) i * x A B := by
    rw [sub_eq_add_neg,← monomial_shift]
    ring
  rw [he]
  fin_cases i
  · rw [monomial_x_zero]
    apply monomial_mem_finite
    norm_num at h ⊢ <;> omega
  · rw [monomial_x_one]
    apply monomial_mem_finite
    norm_num at h ⊢ <;> omega
  · rw [monomial_x_two]
    apply (finiteSpace A B).sub_mem
    · apply (finiteSpace A B).sub_mem
      · apply monomial_mem_finite
        norm_num at h ⊢ <;> omega
      · apply (finiteSpace A B).smul_mem
        apply monomial_mem_finite
        norm_num at h ⊢ <;> omega
    · apply (finiteSpace A B).smul_mem
      apply monomial_mem_finite
      norm_num at h ⊢ <;> omega

theorem finite_generator_y (n : ℤ) (i : Fin 3) (h : n + (i:ℕ) ≤ 0) :
    monomial A B n i * zpow A B (-1) ∈ finiteSpace A B := by
  rw [monomial_shift]
  apply monomial_mem_finite
  omega

theorem infinity_generator_x (n : ℤ) (i : Fin 3) (h : 0 ≤ n) :
    monomial A B n i * x A B ∈ infinitySpace A B := by
  fin_cases i
  · rw [monomial_x_zero]
    exact monomial_mem_infinity A B n 1 h
  · rw [monomial_x_one]
    exact monomial_mem_infinity A B n 2 h
  · rw [monomial_x_two]
    exact (infinitySpace A B).sub_mem
      ((infinitySpace A B).sub_mem (monomial_mem_infinity A B _ _ (by omega))
        ((infinitySpace A B).smul_mem A (monomial_mem_infinity A B _ _ (by omega))))
      ((infinitySpace A B).smul_mem B (monomial_mem_infinity A B _ _ (by omega)))

theorem infinity_generator_z (n : ℤ) (i : Fin 3) (h : 0 ≤ n) :
    monomial A B n i * zpow A B 1 ∈ infinitySpace A B := by
  rw [monomial_shift]
  exact monomial_mem_infinity A B _ _ (by omega)

/-- A generator calculation extends to the complete rational span. -/
theorem span_mul_closed {S : Set (Model A B)} (r : Model A B)
    (h : ∀ a ∈ S, a*r ∈ Submodule.span ℚ S) {a : Model A B}
    (ha : a ∈ Submodule.span ℚ S) : a*r ∈ Submodule.span ℚ S := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · exact h
  · simpa using (Submodule.span ℚ S).zero_mem
  · intro x y _ _ hx hy
    simpa only [add_mul] using (Submodule.span ℚ S).add_mem hx hy
  · intro q x _ hx
    simpa only [smul_mul_assoc] using (Submodule.span ℚ S).smul_mem q hx

theorem finite_mul_x {a : Model A B} (ha : a ∈ finiteSpace A B) :
    a * (x A B * zpow A B (-1)) ∈ finiteSpace A B := by
  apply span_mul_closed A B _ ?_ ha
  rintro _ ⟨n,i,hn,rfl⟩
  exact finite_generator_x A B n i hn

theorem finite_mul_y {a : Model A B} (ha : a ∈ finiteSpace A B) :
    a * zpow A B (-1) ∈ finiteSpace A B := by
  apply span_mul_closed A B _ ?_ ha
  rintro _ ⟨n,i,hn,rfl⟩
  exact finite_generator_y A B n i hn

theorem infinity_mul_x {a : Model A B} (ha : a ∈ infinitySpace A B) :
    a * x A B ∈ infinitySpace A B := by
  apply span_mul_closed A B _ ?_ ha
  rintro _ ⟨n,i,hn,rfl⟩
  exact infinity_generator_x A B n i hn

theorem infinity_mul_z {a : Model A B} (ha : a ∈ infinitySpace A B) :
    a * zpow A B 1 ∈ infinitySpace A B := by
  apply span_mul_closed A B _ ?_ ha
  rintro _ ⟨n,i,hn,rfl⟩
  exact infinity_generator_z A B n i hn

theorem finite_scalar (q : ℚ) : algebraMap ℚ (Model A B) q ∈ finiteSpace A B := by
  have h := (finiteSpace A B).smul_mem q (monomial_mem_finite A B 0 0 (by decide))
  simpa only [monomial,zpow_zero,pow_zero,mul_one,Algebra.smul_def] using h

theorem infinity_scalar (q : ℚ) : algebraMap ℚ (Model A B) q ∈ infinitySpace A B := by
  have h := (infinitySpace A B).smul_mem q (monomial_mem_infinity A B 0 0 (by decide))
  simpa only [monomial,zpow_zero,pow_zero,mul_one,Algebra.smul_def] using h

/-- Residue kills every finite-chart allowed monomial and hence its full span. -/
theorem finite_residue {a : Model A B} (ha : a ∈ finiteSpace A B) : residue A B a = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨n,i,hn,rfl⟩
    rw [residue_monomial]
    apply if_neg
    rintro ⟨rfl,rfl⟩
    norm_num at hn
  · exact map_zero _
  · intro a b _ _ ha hb
    rw [map_add,ha,hb,add_zero]
  · intro q a _ ha
    rw [map_smul,ha,smul_zero]

theorem infinity_residue {a : Model A B} (ha : a ∈ infinitySpace A B) : residue A B a = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨n,i,hn,rfl⟩
    rw [residue_monomial]
    apply if_neg
    rintro ⟨rfl,rfl⟩
    norm_num at hn
  · exact map_zero _
  · intro a b _ _ ha hb
    rw [map_add,ha,hb,add_zero]
  · intro q a _ ha
    rw [map_smul,ha,smul_zero]

end WeierstrassLaurentFiltration318
