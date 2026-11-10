module
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Int.Interval

public section
noncomputable section
namespace LaurentVectorFiltration318
open scoped BigOperators
open LaurentPolynomial
universe u
variable {k : Type u} [Field k] {n : ℕ}

abbrev V (k : Type u) [Field k] (n : ℕ) := Fin n → LaurentPolynomial k

/-- A literal Laurent monomial in one component of the original free module. -/
def monomial (i : Fin n) (a : ℤ) : V k n := Pi.single i (T a)

/-- The exponent filtration on the actual Laurent module, with no quotient or
replacement carrier. -/
def supported (S : Set ℤ) : Submodule k (V k n) :=
  Submodule.span k {v | ∃ i : Fin n, ∃ a ∈ S, v = monomial i a}

lemma monomial_mem {S : Set ℤ} (i : Fin n) (a : ℤ) (ha : a ∈ S) :
    monomial (k:=k) i a ∈ supported S :=
  Submodule.subset_span ⟨i,a,ha,rfl⟩

lemma supported_mono {S T : Set ℤ} (h : S ⊆ T) :
    supported (k:=k) (n:=n) S ≤ supported T := by
  apply Submodule.span_le.mpr
  rintro v ⟨i,a,ha,rfl⟩
  exact monomial_mem i a (h ha)

lemma monomial_shift (i : Fin n) (a b : ℤ) :
    (LaurentPolynomial.T a : LaurentPolynomial k) • monomial (k:=k) i b =
      monomial (k:=k) i (a+b) := by
  ext j
  by_cases h : j=i
  · subst j
    simp only [monomial,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul]
    exact (LaurentPolynomial.T_add a b).symm
  · simp [monomial,Pi.single_apply,h,Ne.symm h]

lemma shift_supported {S T : Set ℤ} (a : ℤ) (h : ∀ b ∈ S, a+b ∈ T)
    {v : V k n} (hv : v ∈ supported S) :
    (LaurentPolynomial.T a : LaurentPolynomial k) • v ∈ supported T := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro v ⟨i,b,hb,rfl⟩
    rw [monomial_shift]
    exact monomial_mem i (a+b) (h b hb)
  · simpa using (supported (k:=k) (n:=n) T).zero_mem
  · intro x y _ _ hx hy
    simpa only [smul_add] using (supported T).add_mem hx hy
  · intro c x _ hx
    rw [smul_comm (LaurentPolynomial.T a) c x]
    exact (supported T).smul_mem c hx

/-- Every original Laurent vector is spanned by its genuine component
monomials. -/
lemma supported_univ (v : V k n) : v ∈ supported Set.univ := by
  have hsingle (i : Fin n) (p : LaurentPolynomial k) :
      Pi.single i p ∈ supported (Set.univ : Set ℤ) := by
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
        have he : (Pi.single i (p+q) : V k n) = (Pi.single i p : V k n) + (Pi.single i q : V k n) := by
          ext j; by_cases h : j=i <;> simp_all [Pi.single_apply]
        rw [he]
        exact (supported Set.univ).add_mem hp hq
    | C_mul_T a c =>
        have he : Pi.single i (C c * T a) = c • monomial (k:=k) i a := by
          ext j
          by_cases h : j=i
          · subst j
            simp [monomial,Pi.single_apply,LaurentPolynomial.smul_eq_C_mul]
          · simp [monomial,Pi.single_apply,h,Ne.symm h]
        rw [he]
        exact (supported Set.univ).smul_mem c (monomial_mem i a (Set.mem_univ _))
  have hv : v = ∑ i : Fin n, Pi.single i (v i) := by
    ext j
    simp [Pi.single_apply]
  rw [hv]
  exact Submodule.sum_mem _ (fun i _ => hsingle i (v i))

/-- Filtration membership forces the actual original coefficients to vanish
outside the specified set. -/
lemma coeff_eq_zero {S : Set ℤ} {v : V k n} (hv : v ∈ supported S)
    (i : Fin n) (a : ℤ) (ha : a ∉ S) : (v i).coeff a = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro v ⟨j,b,hb,rfl⟩
    have hab : b ≠ a := by intro h; subst b; exact ha hb
    by_cases hij : i=j
    · subst j
      simp [monomial,Pi.single_apply,LaurentPolynomial.T_apply,hab]
    · simp [monomial,Pi.single_apply,hij,Ne.symm hij]
  · simp
  · intro x y _ _ hx hy
    simpa using congrArg₂ (·+·) hx hy
  · intro c x _ hx
    simpa using congrArg (fun z : k => c*z) hx

abbrev upper (b : ℤ) : Submodule k (V k n) := supported (Set.Iic b)
abbrev positive : Submodule k (V k n) := supported (Set.Ici 0)
abbrev negative : Submodule k (V k n) := upper 0

lemma upper_mono {a b : ℤ} (h : a ≤ b) :
    upper (k:=k) (n:=n) a ≤ upper b := supported_mono (Set.Iic_subset_Iic.mpr h)

lemma shift_upper (a b : ℤ) {v : V k n} (hv : v ∈ upper b) :
    (LaurentPolynomial.T a : LaurentPolynomial k) • v ∈ upper (a+b) :=
  shift_supported a (fun x hx => by
    change x ≤ b at hx
    change a+x ≤ a+b
    omega) hv

/-- The bound exists because the actual Laurent vector has finite support;
no bound on an unknown line bundle is assumed here. -/
lemma exists_upper (v : V k n) : ∃ b : ℤ, v ∈ upper b := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ (supported_univ v)
  · rintro w ⟨i,a,ha,rfl⟩
    exact ⟨a,monomial_mem i a (by change a ≤ a; exact le_rfl)⟩
  · exact ⟨0,(upper 0).zero_mem⟩
  · rintro x y _ _ ⟨a,ha⟩ ⟨b,hb⟩
    exact ⟨max a b,(upper (max a b)).add_mem
      (upper_mono (le_max_left _ _) ha) (upper_mono (le_max_right _ _) hb)⟩
  · rintro c x _ ⟨a,ha⟩
    exact ⟨a,(upper a).smul_mem c ha⟩
end LaurentVectorFiltration318
