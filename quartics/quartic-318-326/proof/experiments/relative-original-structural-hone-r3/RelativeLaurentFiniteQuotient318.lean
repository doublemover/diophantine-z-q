module
public import RelativePolynomialChartBound318
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace RelativeLaurentFiniteQuotient318
open LaurentPolynomial RelativeLaurentScalar318 RelativeLaurentClearing318
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable (P Q : Submodule R M)

/-- Finite exponent windows of the actual original generators, with no
free-coordinate module or field assumption. -/
def window {r : ℕ} (g : Fin r → M) (N : ℕ) : Submodule R M :=
  Submodule.span R (Set.range (fun p : Fin r × Fin (N+1) =>
    (T (-(p.2.val : ℤ)) : LaurentPolynomial R) • g p.1))

instance window_finite {r : ℕ} (g : Fin r → M) (N : ℕ) :
    Module.Finite R (window R M g N) :=
  Module.Finite.span_of_finite R (Set.finite_range _)

/-- Both original infinite tails lie in the actual two-chart boundary;
the original remaining generators lie in one explicit finite window. -/
lemma boundary_sup_window {r : ℕ} (g : Fin r → M) (N : ℕ)
    (hgP : ∀ i, g i ∈ P)
    (hg : Submodule.span (LaurentPolynomial R) (Set.range g) = ⊤)
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    (hN : ∀ i, (T (-(N : ℤ)) : LaurentPolynomial R) • g i ∈ Q) :
    (P ⊔ Q) ⊔ window R M g N = ⊤ := by
  let S := (P ⊔ Q) ⊔ window R M g N
  have hmono (i : Fin r) (a : ℤ) : (T a : LaurentPolynomial R) • g i ∈ S := by
    by_cases hp : 0 ≤ a
    · exact (le_sup_left : P ⊔ Q ≤ S)
        ((le_sup_left : P ≤ P ⊔ Q) (hP a hp (g i) (hgP i)))
    · by_cases hn : a ≤ -(N : ℤ)
      · apply (le_sup_left : P ⊔ Q ≤ S)
        apply (le_sup_right : Q ≤ P ⊔ Q)
        have h := lower_bound R M Q hQ (b := (N : ℤ)) (d := -a) (by omega) (hN i)
        simpa only [neg_neg] using h
      · apply (le_sup_right : window R M g N ≤ S)
        apply Submodule.subset_span
        refine ⟨(i,⟨(-a).toNat,by omega⟩),?_⟩
        simp only [Int.toNat_of_nonneg (show 0 ≤ -a by omega),neg_neg]
  have hall (x : M) (hx : x ∈ Submodule.span (LaurentPolynomial R) (Set.range g)) :
      ∀ a : ℤ, (T a : LaurentPolynomial R) • x ∈ S := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i,rfl⟩ a
      exact hmono i a
    · intro a
      simpa only [smul_zero] using S.zero_mem
    · intro x y _ _ hx hy a
      simpa only [smul_add] using S.add_mem (hx a) (hy a)
    · intro f x _ hx a
      induction f using LaurentPolynomial.induction_on' with
      | add p q hp hq =>
          simpa only [add_smul,smul_add] using S.add_mem hp hq
      | C_mul_T z c =>
          rw [shift_constant]
          exact S.smul_mem c (hx (a+z))
  apply top_unique
  intro x _
  have hx : x ∈ Submodule.span (LaurentPolynomial R) (Set.range g) := by rw [hg]; trivial
  simpa only [T_zero,one_smul] using hall x hx 0

/-- The original, unshifted two-chart quotient is finite over ANY
coefficient ring. The proof actually constructs a finite window mapping
onto that same quotient; no finite-generation premise on the quotient is
introduced. -/
theorem finite_quotient {r : ℕ} (g : Fin r → M)
    (hgP : ∀ i, g i ∈ P)
    (hg : Submodule.span (LaurentPolynomial R) (Set.range g) = ⊤)
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    (hspanQ : Submodule.span (LaurentPolynomial R) (Q : Set M) = ⊤) :
    Module.Finite R (M ⧸ (P ⊔ Q)) := by
  have hb : ∀ i : Fin r, ∃ b : ℤ, (T (-b) : LaurentPolynomial R) • g i ∈ Q :=
    fun i => by simpa only [Bounded] using exists_bound R M Q hQ hspanQ (g i)
  choose b hb using hb
  let N : ℕ := Finset.univ.sup (fun i : Fin r => (b i).toNat)
  have hN' (i : Fin r) : (T (-(N : ℤ)) : LaurentPolynomial R) • g i ∈ Q := by
    have hi : (b i).toNat ≤ N :=
      Finset.le_sup (f := fun j : Fin r => (b j).toNat) (Finset.mem_univ i)
    exact lower_bound R M Q hQ (by omega) (hb i)
  have hs : Function.Surjective ((P ⊔ Q).mkQ.comp (window R M g N).subtype) := by
    intro q
    obtain ⟨v,rfl⟩ := (P ⊔ Q).mkQ_surjective q
    have hv : v ∈ (P ⊔ Q) ⊔ window R M g N := by
      rw [boundary_sup_window R M P Q g N hgP hg hP hQ hN']
      trivial
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨y,hy⟩,?_⟩
    change (P ⊔ Q).mkQ y = (P ⊔ Q).mkQ v
    have hx0 : (P ⊔ Q).mkQ x = 0 := by
      rw [Submodule.mkQ_apply]
      exact Submodule.Quotient.mk_eq_zero.mpr hx
    rw [← hxy,map_add,hx0,zero_add]
  exact Module.Finite.of_surjective ((P ⊔ Q).mkQ.comp (window R M g N).subtype) hs
end RelativeLaurentFiniteQuotient318
