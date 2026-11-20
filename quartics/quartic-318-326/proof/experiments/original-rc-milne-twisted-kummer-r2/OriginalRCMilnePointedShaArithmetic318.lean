module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

public section

namespace OriginalRCMilnePointedShaArithmetic318

variable {ShaA ShaE ShaK : Type*} [AddCommGroup ShaA] [AddCommGroup ShaE] [AddCommGroup ShaK]
variable [Finite ShaA] [Finite ShaE] [Finite ShaK]

/-- Finite-group step for the SAME two actual pointed Sha maps.
Caller supplies the global duality identifying coker φ with
the dual of ker ψ, not an arbitrary condition containment. -/
theorem finite_sha_cross (φ : ShaA →+ ShaE × ShaK) (ψ : ShaE × ShaK →+ ShaA)
    (hdual : Nat.card ((ShaE × ShaK) ⧸ φ.range) = Nat.card ψ.ker) :
    Nat.card ShaA * Nat.card ψ.ker =
      (Nat.card ShaE * Nat.card ShaK) * Nat.card φ.ker := by
  have hφ := AddSubgroup.card_ker_mul_card_range φ
  have hB := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.range
  calc
    _ = (Nat.card φ.ker * Nat.card φ.range) * Nat.card ψ.ker := by rw [hφ]
    _ = (Nat.card ψ.ker * Nat.card φ.range) * Nat.card φ.ker := by ac_rfl
    _ = _ := by rw [←hdual,←hB,Nat.card_prod]

/-- Orientation and exact consumption of the classical pointed Milne
(7.3.1) kernel ratio. In the intended instantiation the three objects
are the finite 2-primary Sha of Res E, E, and the same companion twist;
their finiteness is from the known forward constituent theorems.
The actual global Milne theorem and the finite-duality comparison
are supplied, not smuggled in as a cardinality theorem of Lean. -/
theorem pointed_sha_read
    (φ : ShaA →+ ShaE × ShaK) (ψ : ShaE × ShaK →+ ShaA)
    (sA sE sK kφ kψ gA nu omegaComp : ℕ)
    (hA : Nat.card ShaA=2^sA) (hE : Nat.card ShaE=2^sE)
    (hK : Nat.card ShaK=2^sK) (hφ : Nat.card φ.ker=2^kφ)
    (hψ : Nat.card ψ.ker=2^kψ)
    (hDual : Nat.card ((ShaE × ShaK) ⧸ φ.range)=Nat.card ψ.ker)
    (hMilne731 : (kφ:ℤ)-kψ =
      (2*(gA:ℤ)-8+1-2*(nu:ℤ))-(-1-2*(omegaComp:ℤ))) :
    (sA:ℤ)-sE-sK=2*(gA:ℤ)-8+(1-2*(nu:ℤ))+1+2*omegaComp := by
  have he := finite_sha_cross φ ψ hDual
  rw [hA,hE,hK,hφ,hψ,←pow_add,←pow_add,←pow_add] at he
  have he' := Nat.pow_right_injective (show 2 ≤ (2:ℕ) by decide) he
  omega

end OriginalRCMilnePointedShaArithmetic318

#print axioms OriginalRCMilnePointedShaArithmetic318.finite_sha_cross
#print axioms OriginalRCMilnePointedShaArithmetic318.pointed_sha_read
