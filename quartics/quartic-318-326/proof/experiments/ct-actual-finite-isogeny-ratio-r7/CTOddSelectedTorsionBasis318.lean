module
public import CTOddSquareclassBasis318
public import OriginalCasselsRamifiedRootCriterion318
public import OriginalCasselsNaturalPrimeValuation318
import CTOriginalPadicValuationPairs318
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public section

noncomputable section

namespace CTOddSelectedTorsionBasis318

open CTOddSquareclassBasis318 ActualTwoDescentSquareClassQuotient318
open OriginalCasselsRamifiedRootCriterion318 OriginalCasselsNaturalPrimeValuation318
open OriginalCasselsOddUnitCharacter318 OriginalCasselsOddUnitSquare318

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem selected_residue_three (n : ℕ) (hr : (n:ZMod 12)=11) :
    (n:ZMod 3)=2 := by
  have hm := (ZMod.natCast_eq_natCast_iff' n 11 12).mp hr
  have h3 : n%3=2 := by rw [←Nat.mod_mod_of_dvd n (by decide : 3∣12),hm]
  exact (ZMod.natCast_eq_natCast_iff' n 2 3).mpr h3

/-- At the retained ternary place the literal torsion labels
(1,n,-3,-3n) exhaust squareclasses, with no local target assumption. -/
theorem ternary_actual_basis (n : ℕ) (hr : (n:ZMod 12)=11) :
    ∃ hN : IsUnit (n:ℤ_[3]),
      Function.Bijective (actualBasis (-3:ℚ_[3]) (by norm_num) (n:ℤ_[3]) hN) := by
  have hR : PadicInt.toZMod (n:ℤ_[3])=(2:ZMod 3) := by
    rw [map_natCast,selected_residue_three n hr]
  have hN := (residue_nonzero_iff_unit (n:ℤ_[3])).mp (by rw [hR]; decide)
  have hNS : ¬ IsSquare (PadicInt.toZMod (n:ℤ_[3])) := by
    rw [hR]
    rintro ⟨z,hz⟩
    exact (by decide : ∀ z : ZMod 3, (2:ZMod 3)≠z*z) z hz
  have hV : (-3:ℚ_[3]).valuation=1 := by
    rw [ActualTwoDescentPadicValuationPairs318.actual_valuation_neg]
    exact Padic.valuation_p
  refine ⟨hN,?_⟩
  exact ⟨actualBasis_injective (by decide) _ _ hV _ hN hNS,
    actualBasis_surjective (by decide) _ _ hV _ hN hNS⟩

section Ramified
variable {p : ℕ} [Fact p.Prime]

private theorem two_ne_residue (hp : 5≤p) : (2:ZMod p)≠0 := by
  intro h
  have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
  exact (by omega : ¬p≤2) (Nat.le_of_dvd (by decide : 0<2) hd)

private theorem three_ne_residue (hp : 5≤p) : (3:ZMod p)≠0 := by
  intro h
  have hd := (ZMod.natCast_eq_zero_iff 3 p).mp h
  exact (by omega : ¬p≤3) (Nat.le_of_dvd (by decide : 0<3) hd)

private theorem negThree_unit (hp : 5≤p) : IsUnit (-3:ℤ_[p]) := by
  apply (residue_nonzero_iff_unit (-3:ℤ_[p])).mp
  simpa only [map_neg,map_ofNat,neg_ne_zero] using three_ne_residue hp

/-- The same quadratic discriminant −3 from the source torsion is
square exactly at the same split residue primes used on the target. -/
theorem residue_negThree_square_iff (hp : 5≤p) :
    IsSquare (PadicInt.toZMod (-3:ℤ_[p])) ↔ p%3=1 := by
  rw [map_neg,map_ofNat,← root_iff_residue_one p hp]
  constructor
  · rintro ⟨s,hs⟩
    let r := (s+1)/2
    have h2 := two_ne_residue hp
    have h4 : (4:ZMod p)≠0 := by
      rw [show (4:ZMod p)=2*2 by ring]
      exact mul_ne_zero h2 h2
    refine ⟨r,?_⟩
    calc
      r^2-r+1=(s*s+3)/4 := by dsimp [r]; field_simp [h2,h4] <;> ring
      _=0 := by rw [←hs,neg_add_cancel,zero_div]
  · rintro ⟨r,hr⟩
    refine ⟨2*r-1,?_⟩
    linear_combination -(4:ZMod p)*hr

theorem ramified_inert_actual_basis (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) (hm : p∈n.primeFactors) (hnSplit : p%3≠1) :
    ∃ hN : IsUnit (-3:ℤ_[p]),
      Function.Bijective (actualBasis (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne') (-3:ℤ_[p]) hN) := by
  obtain ⟨h2,h3⟩ := selected_primeFactors_ne_two_three hn hr hm
  have hp := five_le_prime_of_ne_two_three (Fact.out : p.Prime) h2 h3
  have hN := negThree_unit hp
  have hNS := mt ((residue_negThree_square_iff (p:=p) hp).mp) hnSplit
  have hV := squarefree_support_valuation_one n p hn hs hm
  exact ⟨hN,actualBasis_injective h2 _ _ hV _ hN hNS,
    actualBasis_surjective h2 _ _ hV _ hN hNS⟩

theorem ramified_split_minusThree_class_one (hp : 5≤p) (h2 : p≠2) (hSplit : p%3=1) :
    classOf (-3:ℚ_[p]) (by norm_num)=1 := by
  have hu := negThree_unit hp
  obtain ⟨r,hr,he⟩ := (unit_square_iff_residue h2 (-3:ℤ_[p]) hu).mpr
    ((residue_negThree_square_iff (p:=p) hp).mpr hSplit)
  rw [←class_of_one]
  refine (class_of_eq_iff _ _ _ _).mpr ⟨r,hr,?_⟩
  change PadicInt.Coe.ringHom (-(3:ℤ_[p]))=r^2 at he
  rw [map_neg,map_ofNat] at he
  simpa only [one_mul] using he

end Ramified

end CTOddSelectedTorsionBasis318

#print axioms CTOddSelectedTorsionBasis318.ternary_actual_basis
#print axioms CTOddSelectedTorsionBasis318.ramified_inert_actual_basis
#print axioms CTOddSelectedTorsionBasis318.ramified_split_minusThree_class_one
