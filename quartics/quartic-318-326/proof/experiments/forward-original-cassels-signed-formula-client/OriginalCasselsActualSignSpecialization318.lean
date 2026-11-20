module
public import OriginalCasselsActualSignedProduct318
public import Mathlib.Basic.Finite.Defs
public section

namespace OriginalCasselsActualSignSpecialization318

open OriginalCasselsActualLocalSystem318 OriginalCasselsActualSignedProduct318

/-- Specialize a supplied prime-isogeny sign equation to the verified
local quotients on the same curve. No root number or local scalar is input. -/
theorem signed_of_formula (n : ℕ) (hn : 0 < n) (hs : Squarefree n)
    (hr : (n : ZMod 12) = 11) (r : ℕ)
    (hCassels : (-1 : ℤ)^r = supportProduct (actualLocalSystem n hn hr)) :
    (-1 : ℤ)^r = -1 :=
  hCassels.trans (selected_actual_product n hn hs hr)

theorem nonzero_of_formula (n : ℕ) (hn : 0 < n) (hs : Squarefree n)
    (hr : (n : ZMod 12) = 11) (r : ℕ)
    (hCassels : (-1 : ℤ)^r = supportProduct (actualLocalSystem n hn hr)) :
    r ≠ 0 := by
  intro h0
  have h := signed_of_formula n hn hs hr r hCassels
  rw [h0, pow_zero] at h
  exact (by decide : (1 : ℤ) ≠ -1) h

/-- Application boundary: the actual native dual supplies the finite-case
zero-corank implication; the only arithmetic comparison is the supplied
Cassels equation. The intended instantiation is the full primary Selmer
type, not its rational-point image or its finite-level classes. -/
theorem infinite_of_formula {S : Type*} (n : ℕ) (hn : 0 < n) (hs : Squarefree n)
    (hr : (n : ZMod 12) = 11) (r : ℕ)
    (zero_of_finite : Finite S → r = 0)
    (hCassels : (-1 : ℤ)^r = supportProduct (actualLocalSystem n hn hr)) :
    Infinite S := by
  apply not_finite_iff_infinite.mp
  intro hS
  exact nonzero_of_formula n hn hs hr r hCassels (zero_of_finite hS)

end OriginalCasselsActualSignSpecialization318

#print axioms OriginalCasselsActualSignSpecialization318.signed_of_formula
#print axioms OriginalCasselsActualSignSpecialization318.infinite_of_formula
