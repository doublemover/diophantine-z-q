module
public import OriginalCasselsOddTargetValuation318
public import OriginalCasselsOddLocalFinite318
public import Mathlib.Tactic.FinCases
import all OriginalCasselsOddLocalFinite318
import all OriginalCasselsLiteralIsogenyPoint318
import all OriginalSelectedCasselsParity318
import all OriginalCasselsDyadicXClass318
public section

noncomputable section

namespace OriginalCasselsTernaryLocalCokernel318

open OriginalCasselsOddUnitSquare318 OriginalCasselsOddTargetValuation318
open OriginalCasselsOddLocalFinite318 OriginalCasselsLiteralRangeFinite318
open OriginalCasselsLiteralIsogenyAddition318 OriginalCasselsLiteralIsogenyPoint318
open OriginalCasselsDyadicXClass318 OriginalCasselsTargetClassChord318
open OriginalSelectedCasselsParity318 ActualTwoDescentLocalValuationTools318
open ActualTwoDescentSquareClassQuotient318

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : DecidableEq (ℚ_[3]) := Classical.decEq _

private theorem residue_three (n : ℕ) (hn : (n:ZMod 12)=11) : (n:ZMod 3)=2 := by
  have hm := (ZMod.natCast_eq_natCast_iff' n 11 12).mp hn
  have h3 : n%3=2 := by rw [←Nat.mod_mod_of_dvd n (by decide : 3∣12),hm]
  exact (ZMod.natCast_eq_natCast_iff' n 2 3).mpr h3

private theorem unit_4n (n : ℕ) (hn : (n:ZMod 12)=11) :
    ((4:ℚ_[3])*(n:ℚ_[3])).valuation=0 := by
  have hD : ¬3∣4*n := by
    intro hd
    have he := (ZMod.natCast_eq_zero_iff (4*n) 3).mpr hd
    rw [Nat.cast_mul,residue_three n hn] at he
    exact (by decide : ((4:ZMod 3)*2)≠0) he
  have hv := actual_prime_unit_valuation (p:=3) (4*n) hD
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hv

private theorem residue_unit_split (u : ZMod 3) (hu : u≠0) : u=1 ∨ u=2 := by
  fin_cases u
  · exact (hu rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The exceptional residue-three coefficient at equal valuation is kept
literally. At unit abscissa 1 the abscissa itself is a square. At unit
abscissa 2 the remaining factor is 1 modulo 3, hence a square. -/
theorem ternary_abscissa_square (n : ℕ) (hn : 0<n) (h12 : (n:ZMod 12)=11)
    (x y : ℚ_[3]) (hx : x≠0)
    (he : y^2=x*(x^2-4*(n:ℚ_[3])*x+16*(n:ℚ_[3])^2)) :
    ∃ r : ℚ_[3], r≠0 ∧ x=r^2 := by
  have hnq : (n:ℚ_[3])≠0 := Nat.cast_ne_zero.mpr hn.ne'
  by_cases hv : x.valuation=0
  · let X : ℤ_[3] := ⟨x,(actual_norm_one_of_valuation_zero x hx hv).le⟩
    have hX : (X:ℚ_[3])=x := rfl
    have hU : IsUnit X := PadicInt.isUnit_iff.mpr (actual_norm_one_of_valuation_zero x hx hv)
    have hXr : PadicInt.toZMod X≠0 := (hU.map PadicInt.toZMod).ne_zero
    rcases residue_unit_split _ hXr with hX1|hX2
    · simpa only [hX] using square_of_residue_one (by decide : 3≠2) X hX1
    · apply abscissa_square_of_factor_square (n:ℚ_[3]) x y hx he
      let A : ℤ_[3] := X^2-4*(n:ℤ_[3])*X+16*(n:ℤ_[3])^2
      have hA : PadicInt.toZMod A=1 := by
        simp only [A,map_add,map_sub,map_mul,map_pow,map_ofNat,map_natCast,hX2,residue_three n h12]
        decide
      obtain ⟨s,hs,hsq⟩ := square_of_residue_one (by decide : 3≠2) A hA
      refine ⟨s,hs,?_⟩
      dsimp only [A] at hsq
      push_cast at hsq
      simpa only [hX,Nat.cast_ofNat] using hsq
  · apply abscissa_square_of_factor_square (n:ℚ_[3]) x y hx he
    apply factor_square_of_unequal_val (by decide : 3≠2) _ _ hnq hx
    rwa [unit_4n n h12]

theorem ternary_target_class_one (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11)
    (P : TargetPoint (n:ℚ_[3])) : targetClass P=1 := by
  cases P with
  | zero => rfl
  | some x y H =>
    by_cases hx : x=0
    · subst x
      simp [targetClass]
    · have he : y^2=x*(x^2-4*(n:ℚ_[3])*x+16*(n:ℚ_[3])^2) := by
        have h := H.left
        rw [WeierstrassCurve.Affine.equation_iff] at h
        simp only [targetModel,zero_mul,add_zero,zero_add] at h
        linear_combination h
      change targetClass (targetPoint _ x y (Nat.cast_ne_zero.mpr hn.ne') he)=1
      rw [target_class_at_affine _ hx he,←class_of_one]
      obtain ⟨r,hR,heR⟩ := ternary_abscissa_square n hn hr x y hx he
      apply (class_of_eq_iff _ _ hx one_ne_zero).mpr
      exact ⟨r,hR,by simpa only [one_mul] using heR⟩

/-- Exact cardinal of the literal ternary cokernel; no preselected
local map, quotient size, or Cassels ratio is used. -/
theorem local_ternary_cokernel_card (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    (localOddIsogeny (p:=3) (by decide) (n:ℚ_[3]) (Nat.cast_ne_zero.mpr hn.ne')).cokernelCard=1 := by
  let n₃ : ℚ_[3] := n
  let hn₃ : n₃≠0 := Nat.cast_ne_zero.mpr hn.ne'
  let H : TargetPoint n₃ →+ Additive (SquareClass ℚ_[3]) :=
    xClassHom (actual_target_class_product n₃ hn₃)
  let R : AddSubgroup (Additive (SquareClass ℚ_[3])) :=
    AddMonoidHom.range (G := TargetPoint n₃) (N := Additive (SquareClass ℚ_[3])) H
  have hX : ∀ z : ↥R, z=0 := by
    rintro ⟨z,P,rfl⟩
    apply Subtype.ext
    change targetClass P=1
    exact ternary_target_class_one n hn hr P
  let f : Unit → ↥R := fun _ => 0
  have hF : Function.Bijective f := by
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro z
      exact ⟨(),(hX z).symm⟩
  have e : TargetPoint n₃ ⧸ (literalHom (literal_addition n₃ hn₃)).range ≃+ ↥R :=
    literalQuotientEquiv n₃ hn₃
  change Nat.card (TargetPoint n₃ ⧸ (literalHom (literal_addition n₃ hn₃)).range)=1
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (Equiv.ofBijective f hF).symm,Nat.card_eq_fintype_card] <;> decide

end OriginalCasselsTernaryLocalCokernel318

#print axioms OriginalCasselsTernaryLocalCokernel318.ternary_target_class_one
#print axioms OriginalCasselsTernaryLocalCokernel318.local_ternary_cokernel_card
