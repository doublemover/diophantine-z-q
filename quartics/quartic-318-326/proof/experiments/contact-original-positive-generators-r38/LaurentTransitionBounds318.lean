module
public import LaurentVectorFiltration318

public section
noncomputable section
namespace LaurentTransitionBounds318
open LaurentVectorFiltration318
open scoped BigOperators
universe u
variable {k : Type u} [Field k] {n : ℕ}

/-- The exact original Laurent-linear transition, viewed over the ground field. -/
def underlying (e : V k n ≃ₗ[LaurentPolynomial k] V k n) : V k n →ₗ[k] V k n :=
  e.toLinearMap.restrictScalars k

/-- Every actual finite-rank transition has a uniform exponent bound on its
columns. It is derived from those columns, rather than supplied as an input. -/
lemma exists_column_bound (e : V k n ≃ₗ[LaurentPolynomial k] V k n) :
    ∃ b : ℤ, ∀ i : Fin n, e (monomial i 0) ∈ upper b := by
  choose b hb using fun i : Fin n => exists_upper (e (monomial i 0))
  refine ⟨(Finset.univ.sup (fun i => (b i).toNat) : ℕ),fun i => ?_⟩
  apply upper_mono _ (hb i)
  have hi : (b i).toNat ≤ Finset.univ.sup (fun i => (b i).toNat) :=
    Finset.le_sup (f := fun j : Fin n => (b j).toNat) (Finset.mem_univ i)
  omega

lemma map_monomial (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (i : Fin n) (a : ℤ) :
    e (monomial i a) = (LaurentPolynomial.T a : LaurentPolynomial k) • e (monomial i 0) := by
  have h : monomial (k:=k) i a =
      (LaurentPolynomial.T a : LaurentPolynomial k) • monomial i 0 := by
    simpa only [add_zero] using (monomial_shift (k:=k) i a 0).symm
  rw [h,e.map_smul]

/-- The same original transition shifts the entire exponent filtration by
its derived column bound. -/
lemma map_upper (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (b : ℤ) (hb : ∀ i : Fin n, e (monomial i 0) ∈ upper b)
    (a : ℤ) {v : V k n} (hv : v ∈ upper a) : e v ∈ upper (a+b) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro w ⟨i,c,hc,rfl⟩
    rw [map_monomial]
    exact upper_mono (add_le_add_right hc b) (shift_upper c b (hb i))
  · simpa using (upper (k:=k) (n:=n) (a+b)).zero_mem
  · intro x y _ _ hx hy
    simpa only [map_add] using (upper (a+b)).add_mem hx hy
  · intro c x _ hx
    change underlying e (c • x) ∈ upper (a+b)
    rw [map_smul]
    exact (upper (a+b)).smul_mem c hx

/-- Invertibility forces every sufficiently negative original monomial into
the image of the actual negative chart. -/
lemma negative_tail (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (b : ℤ) (hb : ∀ i : Fin n, e.symm (monomial i 0) ∈ upper b)
    (i : Fin n) (a : ℤ) (ha : a+b ≤ 0) :
    monomial i a ∈ (negative (k:=k) (n:=n)).map (underlying e) := by
  refine ⟨e.symm (monomial i a),?_,?_⟩
  · exact upper_mono ha (map_upper e.symm b hb a (monomial_mem i a (by change a ≤ a; exact le_rfl)))
  · exact e.apply_symm_apply _
end LaurentTransitionBounds318
