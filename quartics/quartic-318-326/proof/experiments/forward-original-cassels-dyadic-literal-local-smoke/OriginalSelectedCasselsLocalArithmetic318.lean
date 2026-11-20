module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public section

namespace OriginalSelectedCasselsLocalArithmetic318
open scoped BigOperators

/-- Exact affine chart of the classical quotient by (0,0). This does
not itself assert that the rational formulas extend to a morphism. -/
theorem affine_isogeny_chart {F : Type*} [Field F] (n x y : F) (hx : x ≠ 0)
    (hy : y^2 = x*(x-n)*(x+3*n)) :
    let X := x+2*n-3*n^2/x
    let Y := y+3*n^2*y/x^2
    Y^2 = X*(X^2-4*n*X+16*n^2) := by
  dsimp only
  calc
    _ = y^2*(1+3*n^2/x^2)^2 := by ring
    _ = _ := by rw [hy]; field_simp [hx] <;> ring

/-- True finite unit obstruction in the dyadic valuation cases 0,2,4
on the target equation. The intermediate valuation 2 cannot yield
a square ordinate since n ≡ 3 mod 4. -/
theorem dyadic_unit_rows : ∀ n u : ZMod 8,
    (n = 3 ∨ n = 7) → (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) →
    (u^2-4*n*u+16*n^2 = 5) ∧
      (u*(u^2-n*u+n^2) ≠ 1) ∧ (16*u^2-4*n*u+n^2 = 5) := by decide

/-- This only encodes the arithmetic local *isogeny ratio sign* at
p|n, not an epsilon factor or a native Cassels formula. -/
@[expose] def residue3Sign : ZMod 3 →* ℤ where
  toFun x := if x = 0 then 0 else if x = 1 then 1 else -1
  map_one' := by decide
  map_mul' := by decide

theorem selected_ramified_product {ι : Type*} (S : Finset ι) (p : ι → ℕ) (n : ℕ)
    (hprod : ∏ i ∈ S, p i = n) (hr : (n : ZMod 12) = 11) :
    ∏ i ∈ S, residue3Sign (p i : ZMod 3) = -1 := by
  have h12 : n % 12 = 11 := by
    have hh := congrArg ZMod.val hr
    norm_num only [ZMod.val_natCast] at hh
    exact hh
  have hmod : n % 3 = 2 := by
    rw [← Nat.mod_mod_of_dvd n (by decide : 3 ∣ 12), h12]
  have h3 : (n : ZMod 3) = (2 : ℕ) :=
    (ZMod.natCast_eq_natCast_iff' n 2 3).mpr hmod
  rw [← map_prod, ← Nat.cast_prod, hprod, h3] <;> decide

/-- The real, dyadic, and ternary signs are respectively −1,+1,−1.
Good finite factors are one. This is the final product of the local
ratios on the actual squarefree selected parameter, not yet its
Selmer dimension. -/
theorem selected_product (n : ℕ) (hs : Squarefree n) (hr : (n : ZMod 12) = 11) :
    (-1 : ℤ) * 1 * (-1) * (∏ p ∈ n.primeFactors, residue3Sign (p : ZMod 3)) = -1 := by
  rw [selected_ramified_product n.primeFactors id n (Nat.prod_primeFactors_of_squarefree hs) hr] <;> decide

end OriginalSelectedCasselsLocalArithmetic318

#print axioms OriginalSelectedCasselsLocalArithmetic318.affine_isogeny_chart
#print axioms OriginalSelectedCasselsLocalArithmetic318.dyadic_unit_rows
#print axioms OriginalSelectedCasselsLocalArithmetic318.selected_product
