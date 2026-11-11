module
public import RelativeLaurentPositiveClearing318
public import RelativePolynomialChartBound318
public section
noncomputable section
namespace FiniteLaurentSectionExtension318
open LaurentPolynomial RelativeLaurentScalar318
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
  [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
set_option maxHeartbeats 650000

/-- A finite prescribed family extends across the reciprocal chart at
EVERY sufficiently large twist. The bound is produced by denominator
clearing, not by a global-generation assumption. -/
theorem negative {r : ℕ} (g : Fin r → M) (Q : Submodule R M)
    (hQ : ∀ a : ℤ, a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    (hspan : Submodule.span (LaurentPolynomial R) (Q : Set M) = ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i,
      (T (-(n : ℤ)) : LaurentPolynomial R) • g i ∈ Q := by
  have hb : ∀ i, ∃ b : ℤ, (T (-b) : LaurentPolynomial R) • g i ∈ Q :=
    fun i => RelativeLaurentClearing318.exists_bound R M Q hQ hspan (g i)
  choose b hb using hb
  let N := Finset.univ.sup (fun i : Fin r => (b i).toNat)
  refine ⟨N,fun n hn i => ?_⟩
  apply RelativeLaurentClearing318.lower_bound R M Q hQ _ (hb i)
  have hi : (b i).toNat ≤ N := Finset.le_sup (f := fun j : Fin r => (b j).toNat)
    (Finset.mem_univ i)
  omega

/-- The opposite direction uses the actual positive Laurent action; it
is not obtained by forgetting the reciprocal coordinate convention. -/
theorem positive {r : ℕ} (g : Fin r → M) (P : Submodule R M)
    (hP : ∀ a : ℤ, 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    (hspan : Submodule.span (LaurentPolynomial R) (P : Set M) = ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i,
      (T (n : ℤ) : LaurentPolynomial R) • g i ∈ P := by
  have hb : ∀ i, ∃ b : ℤ, (T b : LaurentPolynomial R) • g i ∈ P :=
    fun i => RelativeLaurentPositiveClearing318.exists_bound R M P hP hspan (g i)
  choose b hb using hb
  let N := Finset.univ.sup (fun i : Fin r => (b i).toNat)
  refine ⟨N,fun n hn i => ?_⟩
  apply RelativeLaurentPositiveClearing318.upper_bound R M P hP _ (hb i)
  have hi : (b i).toNat ≤ N := Finset.le_sup (f := fun j : Fin r => (b j).toNat)
    (Finset.mem_univ i)
  omega
end FiniteLaurentSectionExtension318
