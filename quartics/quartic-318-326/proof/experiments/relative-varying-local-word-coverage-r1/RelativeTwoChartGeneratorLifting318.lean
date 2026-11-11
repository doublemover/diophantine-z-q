module
public import RelativeLaurentPositiveClearing318
public import RelativeLaurentGeneratorBound318
public section
noncomputable section
namespace RelativeTwoChartGeneratorLifting318
open LaurentPolynomial RelativeLaurentScalar318
set_option maxHeartbeats 650000
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable (P Q : Submodule R M)

/-- A SINGLE positive bound extends both finite chart families across
the opposite whole chart. The two directions use the actual reciprocal
Laurent actions, not an identification of finite and infinity coordinates. -/
theorem exists_bound {r s : ℕ} (g : Fin r → M) (h : Fin s → M)
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    (hspanP : Submodule.span (LaurentPolynomial R) (P : Set M) = ⊤)
    (hspanQ : Submodule.span (LaurentPolynomial R) (Q : Set M) = ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ i, (T (-(n : ℤ)) : LaurentPolynomial R) • g i ∈ Q) ∧
      (∀ j, (T (n : ℤ) : LaurentPolynomial R) • h j ∈ P) := by
  have hg : ∀ i : Fin r, ∃ b : ℤ, (T (-b) : LaurentPolynomial R) • g i ∈ Q :=
    fun i => RelativeLaurentClearing318.exists_bound R M Q hQ hspanQ (g i)
  have hh : ∀ j : Fin s, ∃ b : ℤ, (T b : LaurentPolynomial R) • h j ∈ P :=
    fun j => RelativeLaurentPositiveClearing318.exists_bound R M P hP hspanP (h j)
  choose b hb using hg
  choose d hd using hh
  let N : ℕ := max (Finset.univ.sup (fun i : Fin r => (b i).toNat))
    (Finset.univ.sup (fun j : Fin s => (d j).toNat))
  refine ⟨N,fun n hn => ⟨?_,?_⟩⟩
  · intro i
    apply RelativeLaurentClearing318.lower_bound R M Q hQ (b := b i) (d := n) _ (hb i)
    have hi := Finset.le_sup (f := fun k : Fin r => (b k).toNat) (Finset.mem_univ i)
    have hN : Finset.univ.sup (fun k : Fin r => (b k).toNat) ≤ N := le_max_left _ _
    omega
  · intro j
    apply RelativeLaurentPositiveClearing318.upper_bound R M P hP (b := d j) (d := n) _ (hd j)
    have hj := Finset.le_sup (f := fun k : Fin s => (d k).toNat) (Finset.mem_univ j)
    have hN : Finset.univ.sup (fun k : Fin s => (d k).toNat) ≤ N := le_max_right _ _
    omega
end RelativeTwoChartGeneratorLifting318
