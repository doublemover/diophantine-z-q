module
public import RelativeLaurentClearing318
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Choose
public section
noncomputable section
namespace RelativeLaurentGeneratorBound318
open LaurentPolynomial RelativeLaurentScalar318 RelativeLaurentClearing318
set_option maxHeartbeats 650000
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable (P Q : Submodule R M)

/-- The actual two-chart coefficient boundary, with the original Laurent
monomial action. No free presentation or invertible matrix is introduced. -/
def boundary (n : ℤ) : Submodule R M := P ⊔ Q.map (shift R M n)

/-- A finite original generating family lying in the positive chart and
localization of the negative chart give ONE bound for all larger twists,
over ANY commutative coefficient ring, including nonreduced rings. -/
theorem exists_boundary_bound {r : ℕ} (g : Fin r → M)
    (hgP : ∀ i, g i ∈ P)
    (hg : Submodule.span (LaurentPolynomial R) (Set.range g) = ⊤)
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    (hspanQ : Submodule.span (LaurentPolynomial R) (Q : Set M) = ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → boundary R M P Q (n : ℤ) = ⊤ := by
  have hb : ∀ i : Fin r, ∃ b : ℤ, (T (-b) : LaurentPolynomial R) • g i ∈ Q :=
    fun i => by simpa only [Bounded] using exists_bound R M Q hQ hspanQ (g i)
  choose b hb using hb
  let N : ℕ := Finset.univ.sup (fun i : Fin r => (b i).toNat)
  have hNb (i : Fin r) : b i ≤ (N : ℤ) := by
    have hi : (b i).toNat ≤ N := by
      exact Finset.le_sup (f := fun j : Fin r => (b j).toNat) (Finset.mem_univ i)
    omega
  refine ⟨N,fun n hn => ?_⟩
  have hgn (i : Fin r) : (T (-(n : ℤ)) : LaurentPolynomial R) • g i ∈ Q :=
    lower_bound R M Q hQ (by have hi := hNb i; omega) (hb i)
  have hmono (i : Fin r) (a : ℤ) : (T a : LaurentPolynomial R) • g i ∈ boundary R M P Q n := by
    by_cases ha : 0 ≤ a
    · exact (le_sup_left : P ≤ boundary R M P Q n) (hP a ha (g i) (hgP i))
    · apply (le_sup_right : Q.map (shift R M n) ≤ boundary R M P Q n)
      refine ⟨(T a : LaurentPolynomial R) • ((T (-(n : ℤ)) : LaurentPolynomial R) • g i),
        hQ a (by omega) _ (hgn i),?_⟩
      change (T (n : ℤ) : LaurentPolynomial R) •
        ((T a : LaurentPolynomial R) • ((T (-(n : ℤ)) : LaurentPolynomial R) • g i)) = _
      rw [shift_add,shift_add]
      have he : (n : ℤ)+a+(-(n : ℤ)) = a := by omega
      rw [he]
  have hall (x : M) (hx : x ∈ Submodule.span (LaurentPolynomial R) (Set.range g)) :
      ∀ a : ℤ, (T a : LaurentPolynomial R) • x ∈ boundary R M P Q n := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i,rfl⟩ a
      exact hmono i a
    · intro a
      simpa only [smul_zero] using (boundary R M P Q n).zero_mem
    · intro x y _ _ hx hy a
      simpa only [smul_add] using (boundary R M P Q n).add_mem (hx a) (hy a)
    · intro f x _ hx a
      induction f using LaurentPolynomial.induction_on' with
      | add p q hp hq =>
          simpa only [add_smul,smul_add] using (boundary R M P Q n).add_mem hp hq
      | C_mul_T z c =>
          rw [shift_constant]
          exact (boundary R M P Q n).smul_mem c (hx (a+z))
  apply top_unique
  intro x hx
  have hx' : x ∈ Submodule.span (LaurentPolynomial R) (Set.range g) := by rw [hg]; trivial
  simpa only [T_zero,one_smul] using hall x hx' 0

/-- The actual coefficient quotient vanishes uniformly beyond that one
bound. This is algebraic preparation; no geometric H1 identification or
nonreduced affine acyclicity is assumed implicitly. -/
theorem exists_quotient_bound {r : ℕ} (g : Fin r → M)
    (hgP : ∀ i, g i ∈ P)
    (hg : Submodule.span (LaurentPolynomial R) (Set.range g) = ⊤)
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    (hspanQ : Submodule.span (LaurentPolynomial R) (Q : Set M) = ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : M ⧸ boundary R M P Q (n : ℤ), x = 0 := by
  obtain ⟨N,hN⟩ := exists_boundary_bound R M P Q g hgP hg hP hQ hspanQ
  refine ⟨N,fun n hn x => ?_⟩
  obtain ⟨y,rfl⟩ := (boundary R M P Q (n : ℤ)).mkQ_surjective x
  rw [Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  rw [hN n hn]
  trivial
end RelativeLaurentGeneratorBound318
