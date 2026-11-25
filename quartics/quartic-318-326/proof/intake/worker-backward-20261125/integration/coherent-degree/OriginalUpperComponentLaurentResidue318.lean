module
public import LaurentCechFinite318

public section
noncomputable section
namespace OriginalUpperComponentLaurentResidue318

open LaurentPolynomial LaurentVectorFiltration318 LaurentTransitionBounds318
open scoped BigOperators
universe u
variable {k : Type u} [Field k] {n : ℕ}

/-- The coefficient pairing on the original Laurent overlap, using the dt frame.
This is not the field trace and has no separability restriction on a pencil. -/
def residuePair (u v : V k n) : k :=
  ∑ i, (u i * v i).coeff (-1)

lemma pair_comm (u v : V k n) : residuePair u v = residuePair v u := by
  unfold residuePair
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- Curried in the right entry to use the original quotient linear map. -/
def linearLeft (v : V k n) : V k n →ₗ[k] k where
  toFun u := residuePair u v
  map_add' u w := by
    simp only [residuePair, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c u := by
    simp only [residuePair, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_mul_assoc, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]

@[simp]
theorem linearLeft_apply (v u : V k n) : linearLeft v u = residuePair u v := rfl

theorem pair_monomial (i : Fin n) (a : ℤ) (v : V k n) :
    residuePair (monomial i a) v = (v i).coeff (-1 - a) := by
  classical
  unfold residuePair
  rw [Finset.sum_eq_single i]
  · rw [monomial, Pi.single_eq_same]
    have ha : a + (-1 - a) = -1 := by omega
    simpa only [LaurentPolynomial.T, ha, one_mul] using
      (AddMonoidAlgebra.coeff_single_mul_add (v i) (1 : k) a (-1 - a))
  · intro j _ hji
    simp [monomial, Pi.single_apply, hji, Ne.symm hji]
  · simp

/-- On the overlap the pure Laurent residue sees the coefficient with exponent
opposite to the other exponent minus one, in the very same component. -/
theorem pair_monomials (i j : Fin n) (a b : ℤ) :
    residuePair (monomial (k := k) i a) (monomial j b) =
      if i = j ∧ a + b = -1 then 1 else 0 := by
  rw [pair_monomial]
  by_cases h : i = j
  · subst j
    have he : b = -1 - a ↔ a + b = -1 := by omega
    simp [monomial, LaurentPolynomial.T_apply, he]
  · simp [monomial, Pi.single_apply, h, Ne.symm h]

theorem pair_separates (v : V k n) (hv : ∀ u, residuePair u v = 0) : v = 0 := by
  funext i
  apply LaurentPolynomial.ext
  intro b
  have h := hv (monomial i (-1 - b))
  rw [pair_monomial, show -1 - (-1 - b) = b by omega] at h
  simpa using h

/-- The span of exactly the listed monomials tests an annihilator, with no
infinite product of coefficients or completed Laurent series. -/
theorem annihilates_supported_iff (S : Set ℤ) (v : V k n) :
    (∀ u ∈ supported S, residuePair u v = 0) ↔
      ∀ (i : Fin n) (a : ℤ), a ∈ S → (v i).coeff (-1 - a) = 0 := by
  constructor
  · intro h i a ha
    simpa only [pair_monomial] using h _ (monomial_mem i a ha)
  · intro h u hu
    change linearLeft v u = 0
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro w ⟨i, a, ha, rfl⟩
      rw [linearLeft_apply, pair_monomial]
      exact h i a ha
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro c x _ hx
      rw [map_smul, hx, smul_zero]

/-- Every functional on this actual Čech cokernel comes from a finite Laurent
vector. Its representative uses the same finite window already proved to
exhaust the cokernel; every exponent outside the window is tested too. -/
theorem represents (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (f : LaurentCechFinite318.H1 e →ₗ[k] k) :
    ∃! v : V k n, ∀ u, residuePair u v = f ((LaurentCechFinite318.boundary e).mkQ u) := by
  classical
  obtain ⟨b, hb⟩ := exists_column_bound e.symm
  let Q := LaurentCechFinite318.boundary e
  let S := Finset.Icc (-b + 1) (-1)
  let ℓ : V k n →ₗ[k] k := f.comp Q.mkQ
  let v : V k n :=
    ∑ i : Fin n, ∑ a ∈ S, ℓ (monomial i a) • monomial i (-1 - a)
  have hz {i : Fin n} {a : ℤ} (ha : a ∉ S) : ℓ (monomial i a) = 0 := by
    have hm : monomial (k := k) i a ∈ Q := by
      by_cases hpos : 0 ≤ a
      · exact (le_sup_left : positive ≤ Q) (monomial_mem i a hpos)
      · have hneg : a + b ≤ 0 := by
          rw [Finset.mem_Icc] at ha
          omega
        exact (le_sup_right : negative.map (underlying e) ≤ Q) (negative_tail e b hb i a hneg)
    show f (Q.mkQ (monomial i a)) = 0
    rw [Submodule.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
  have hm (i : Fin n) (a : ℤ) : residuePair (monomial i a) v = ℓ (monomial i a) := by
    rw [pair_comm]
    change linearLeft (monomial i a) v = ℓ (monomial i a)
    simp only [v, map_sum, map_smul, linearLeft_apply, pair_monomials]
    have hindex (j : Fin n) (c : ℤ) :
        (j = i ∧ (-1 - c) + a = -1) ↔ j = i ∧ c = a := by
      constructor <;> rintro ⟨hji, hca⟩ <;> exact ⟨hji, by omega⟩
    simp only [hindex]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · by_cases ha : a ∈ S
      · rw [Finset.sum_eq_single_of_mem a ha]
        · simp
        · intro c _ hca
          simp [hca]
      · rw [hz ha]
        apply Finset.sum_eq_zero
        intro c hc
        have hca : c ≠ a := fun h => ha (h ▸ hc)
        simp [hca]
    · intro j _ hji
      apply Finset.sum_eq_zero
      intro c _
      simp [hji]
  have hall (u : V k n) : residuePair u v = ℓ u := by
    change linearLeft v u = ℓ u
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (supported_univ u)
    · rintro w ⟨i, a, _, rfl⟩
      exact hm i a
    · rw [map_zero, map_zero]
    · intro x y _ _ hx hy
      rw [map_add, map_add, hx, hy]
    · intro c x _ hx
      rw [map_smul, map_smul, hx]
  refine ⟨v, hall, ?_⟩
  intro w hw
  have hcoeff (i : Fin n) (a : ℤ) : (w i).coeff a = (v i).coeff a := by
    have he := (hw (monomial i (-1 - a))).trans (hall _).symm
    rw [pair_monomial, pair_monomial, show -1 - (-1 - a) = a by omega] at he
    exact he
  funext i
  exact LaurentPolynomial.ext (hcoeff i)

end OriginalUpperComponentLaurentResidue318
