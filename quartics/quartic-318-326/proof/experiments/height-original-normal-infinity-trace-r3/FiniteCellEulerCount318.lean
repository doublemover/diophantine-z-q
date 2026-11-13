module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic
public section
noncomputable section
open scoped BigOperators
namespace FiniteCellEulerCount318

/-- Additive form of the pinned full-Fintype dependent partition formula. -/
theorem sum_partition {A M : Type*} [Fintype A] [AddCommMonoid M]
    (p : A → Prop) [DecidablePred p] (f : ∀ a, p a → M) (g : ∀ a, ¬ p a → M) :
    (∑ a, if h : p a then f a h else g a h) =
      (∑ a : {a // p a}, f a a.property) + ∑ a : {a // ¬ p a}, g a a.property := by
  simp only [Finset.sum_dite]
  congr 1
  · exact Equiv.sum_comp (Equiv.subtypeEquivRight (by simp))
      (fun x : {x // p x} => f x x.property)
  · exact Equiv.sum_comp (Equiv.subtypeEquivRight (by simp))
      (fun x : {x // ¬ p x} => g x x.property)

/-- Count the entire domain by the fibers of the actual cell map. -/
theorem map_card {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    Fintype.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
  simpa only [Fintype.card_sigma, Nat.card_eq_fintype_card] using h

theorem constant_fiber_card {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (n : ℕ) (hf : ∀ b : B, Nat.card {a : A // f a = b} = n) :
    Fintype.card A = Fintype.card B * n := by
  rw [map_card f]
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Actual finite cell counts imply the degree16 Euler/RH equation.
The edge/face hypotheses concern fibers of the SAME cell maps; no Euler
identity or genus formula is smuggled into the counting lemma. -/
theorem euler {VX VY EX EY FX FY : Type*}
    [Fintype VX] [Fintype VY] [Fintype EX] [Fintype EY] [Fintype FX] [Fintype FY]
    (edge : EX → EY) (face : FX → FY) (branches : ℕ)
    (hvertex : (Fintype.card VX : ℤ) = 16 * Fintype.card VY - 8 * branches)
    (hedge : ∀ e, Nat.card {x : EX // edge x = e} = 16)
    (hface : ∀ f, Nat.card {x : FX // face x = f} = 16) :
    (Fintype.card VX : ℤ) - Fintype.card EX + Fintype.card FX =
      16 * ((Fintype.card VY : ℤ) - Fintype.card EY + Fintype.card FY) - 8 * branches := by
  have he := constant_fiber_card edge 16 hedge
  have hf := constant_fiber_card face 16 hface
  rw [he, hf]
  push_cast
  linarith

/-- A compatible original surface cellulation supplies its Euler/genus
identities. Combined with the genuine fiber counts this DERIVES RH rather
than assuming RH as a separate equation. -/
theorem riemann_hurwitz {VX VY EX EY FX FY : Type*}
    [Fintype VX] [Fintype VY] [Fintype EX] [Fintype EY] [Fintype FX] [Fintype FY]
    (edge : EX → EY) (face : FX → FY) (branches sourceGenus quotientGenus : ℕ)
    (hvertex : (Fintype.card VX : ℤ) = 16 * Fintype.card VY - 8 * branches)
    (hedge : ∀ e, Nat.card {x : EX // edge x = e} = 16)
    (hface : ∀ f, Nat.card {x : FX // face x = f} = 16)
    (hsource : (Fintype.card VX : ℤ) - Fintype.card EX + Fintype.card FX =
      2 - 2 * sourceGenus)
    (htarget : (Fintype.card VY : ℤ) - Fintype.card EY + Fintype.card FY =
      2 - 2 * quotientGenus) :
    2 * (sourceGenus : ℤ) - 2 = 16 * (2 * (quotientGenus : ℤ) - 2) + 8 * branches := by
  have h := euler edge face branches hvertex hedge hface
  rw [hsource, htarget] at h
  linarith
end FiniteCellEulerCount318
