module
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
public section

namespace OriginalSelectedLocalRootSigns318
open scoped BigOperators

private theorem residue12 (n : ℕ) (hr : (n:ZMod 12)=11) : n % 12 = 11 :=
  (ZMod.natCast_eq_natCast_iff' n 11 12).mp hr

/-- The actual squarefree prime divisors in this selected class are away
from both old local primes. No odd-factor support is supplied ad hoc. -/
theorem selected_prime_factors (n p : ℕ) (hr : (n:ZMod 12)=11)
    (hp : p ∈ n.primeFactors) : p.Prime ∧ 5 ≤ p ∧ p ∣ n := by
  obtain ⟨hP,hd,_⟩ := Nat.mem_primeFactors.mp hp
  have hres := residue12 n hr
  have h2 : p ≠ 2 := by
    intro he
    rw [he] at hd
    have h := (Nat.dvd_iff_mod_eq_zero).mp hd
    omega
  have h3 : p ≠ 3 := by
    intro he
    rw [he] at hd
    have h := (Nat.dvd_iff_mod_eq_zero).mp hd
    omega
  have h4 : p ≠ 4 := by
    intro he
    rw [he] at hP
    exact (by decide : ¬ Nat.Prime 4) hP
  have hp2 := hP.two_le
  exact ⟨hP,by omega,hd⟩

/-- Multiplication of the literal good-prime signs (the quadratic
character χ₄) on the squarefree list of prime divisors. -/
theorem selected_good_prime_product (n : ℕ) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) :
    (∏ p ∈ n.primeFactors, ZMod.χ₄ (p:ZMod 4)) = -1 := by
  have hres := residue12 n hr
  calc
    _ = ZMod.χ₄ (∏ p ∈ n.primeFactors, (p:ZMod 4)) := (map_prod ZMod.χ₄ _ _).symm
    _ = ZMod.χ₄ (n:ZMod 4) := by
      rw [←map_prod (Nat.castRingHom (ZMod 4)),Nat.prod_primeFactors_of_squarefree hs]
    _ = -1 := ZMod.χ₄_nat_three_mod_four (by omega)

/-- The finite support product has the exact real factor and two old
factors for the literal models. This records the standard local/global
root-number inputs but does NOT define elliptic epsilon factors. -/
structure LocalRootNumberInput (W : ℕ → ℤ) (localW : ℕ → ℕ → ℤ) : Prop where
  factorization : ∀ n : ℕ, 0<n → Squarefree n → (n:ZMod 12)=11 →
    W n = (-1) * localW 2 n * localW 3 n * ∏ p ∈ n.primeFactors, localW p n
  ramifiedGood : ∀ n p : ℕ, 0<n → Squarefree n → (n:ZMod 12)=11 →
    ∀ [Fact (Nat.Prime p)], 5 ≤ p → p ∣ n → localW p n = legendreSym p (-1)
  isoTwo : ∀ n r : ℕ, (n:ZMod 12)=11 → (r:ZMod 12)=11 →
    n % 8 = r % 8 → localW 2 n = localW 2 r
  isoThree : ∀ n r : ℕ, (n:ZMod 12)=11 → (r:ZMod 12)=11 →
    n % 3 = r % 3 → localW 3 n = localW 3 r

/-- The odd prime product exactly cancels the real factor. -/
theorem old_local_product (W : ℕ → ℤ) (localW : ℕ → ℕ → ℤ)
    (root : LocalRootNumberInput W localW) (n : ℕ)
    (hp : 0<n) (hs : Squarefree n) (hr : (n:ZMod 12)=11) :
    W n = localW 2 n * localW 3 n := by
  have hprod : (∏ p ∈ n.primeFactors, localW p n) = -1 := by
    rw [←selected_good_prime_product n hs hr]
    apply Finset.prod_congr rfl
    intro p hpn
    obtain ⟨hP,h5,hd⟩ := selected_prime_factors n p hr hpn
    letI : Fact (Nat.Prime p) := ⟨hP⟩
    exact (root.ramifiedGood n p hp hs hr h5 hd).trans
      (legendreSym.at_neg_one (by omega : p ≠ 2))
  rw [root.factorization n hp hs hr,hprod]
  ring

/-- Calibrate both selected slots using the same true W and its local
factors. The only numerical reference data required are the two signs. -/
theorem calibrated_negative (W : ℕ → ℤ) (localW : ℕ → ℕ → ℤ)
    (root : LocalRootNumberInput W localW) (w11 : W 11 = -1) (w23 : W 23 = -1)
    (n : ℕ) (hp : 0<n) (hs : Squarefree n) (hr : (n:ZMod 12)=11) :
    W n = -1 := by
  have hn := residue12 n hr
  have hslot : n % 24 = 11 ∨ n % 24 = 23 := by omega
  have hcmp (r : ℕ) (hpos : 0<r) (hsq : Squarefree r) (hrr : (r:ZMod 12)=11)
      (hm : n % 24 = r % 24) : W n = W r := by
    rw [old_local_product W localW root n hp hs hr,old_local_product W localW root r hpos hsq hrr,
      root.isoTwo n r hr hrr (by omega),root.isoThree n r hr hrr (by omega)]
  rcases hslot with h | h
  · exact (hcmp 11 (by decide) (Nat.Prime.squarefree (by decide : Nat.Prime 11))
      (by decide) (by omega)).trans w11
  · exact (hcmp 23 (by decide) (Nat.Prime.squarefree (by decide : Nat.Prime 23))
      (by decide) (by omega)).trans w23

end OriginalSelectedLocalRootSigns318

#print axioms OriginalSelectedLocalRootSigns318.selected_good_prime_product
#print axioms OriginalSelectedLocalRootSigns318.calibrated_negative
