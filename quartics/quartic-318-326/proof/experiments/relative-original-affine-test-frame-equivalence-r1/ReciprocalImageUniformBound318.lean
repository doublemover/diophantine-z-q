module
public import FiniteLaurentVectorFiltration318
public import Mathlib.RingTheory.Finiteness.Defs
public section
noncomputable section
namespace ReciprocalImageUniformBound318
open LaurentPolynomial FiniteLaurentVectorFiltration318
set_option maxHeartbeats 800000
universe u v w
variable (R : Type u) [CommRing R] {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma constant_smul (r : R) (v : V R ι) : (C r : LaurentPolynomial R) • v = r • v := by
  ext i
  exact (LaurentPolynomial.smul_eq_C_mul r (v i)).symm

/-- Arbitrary reciprocal polynomials preserve one fixed upper exponent
bound, including nilpotent coefficients over an arbitrary base ring. -/
lemma negative_stable (b : ℤ) (p : Polynomial R) (v : V R ι) (hv : v ∈ upper b) :
    (invert (Polynomial.toLaurent p) : LaurentPolynomial R) • v ∈ upper b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add,add_smul] using (upper b).add_mem hp hq
  | monomial m r =>
    rw [Polynomial.toLaurent_C_mul_T,map_mul,invert_C,invert_T,mul_smul,constant_smul]
    apply (upper b).smul_mem r
    exact upper_mono (show -(m : ℤ)+b ≤ b by omega) (shift_upper (-(m : ℤ)) b hv)

variable (N : Type v) [AddCommGroup N] [Module (Polynomial R) N] [Module.Finite (Polynomial R) N]
  (M : Type w) [AddCommGroup M] [Module (LaurentPolynomial R) M]
  (ψ : N →+ M)
  (hψ : ∀ p : Polynomial R, ∀ x : N,
    ψ (p • x) = (invert (Polynomial.toLaurent p) : LaurentPolynomial R) • ψ x)
  (J : M →ₗ[LaurentPolynomial R] V R ι)

include hψ in
/-- A finite ORIGINAL opposite-chart generating family supplies ONE
uniform upper bound for the full original reciprocal image under any
actual Laurent-linear coordinate map. No bound on unknown global sections
is assumed. -/
theorem exists_bound : ∃ b : ℕ, ∀ x : N, J (ψ x) ∈ upper (b : ℤ) := by
  obtain ⟨r,g,hg⟩ := Module.Finite.exists_fin (R := Polynomial R) (M := N)
  choose a ha using fun i : Fin r => exists_upper (J (ψ (g i)))
  let b : ℕ := Finset.univ.sup (fun i : Fin r => (a i).toNat)
  have hb (i : Fin r) : a i ≤ (b : ℤ) := by
    have h : (a i).toNat ≤ b := Finset.le_sup (f := fun j : Fin r => (a j).toNat) (Finset.mem_univ i)
    omega
  refine ⟨b,fun x => ?_⟩
  have hx : x ∈ Submodule.span (Polynomial R) (Set.range g) := by rw [hg]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i,rfl⟩
    exact upper_mono (hb i) (ha i)
  · simpa only [map_zero] using (upper (b : ℤ) : Submodule R (V R ι)).zero_mem
  · intro x y _ _ hx hy
    simpa only [map_add] using (upper (b : ℤ) : Submodule R (V R ι)).add_mem hx hy
  · intro p x _ hx
    rw [hψ,map_smul]
    exact negative_stable R (b : ℤ) p (J (ψ x)) hx
end ReciprocalImageUniformBound318
