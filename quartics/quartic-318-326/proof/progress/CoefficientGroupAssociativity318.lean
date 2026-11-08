module
public import CoefficientPointGroup318
public section
noncomputable section
namespace CoefficientGroupAssociativity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CoefficientSchemePoints318 CompletedAdditionTriple318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S]
local notation "R" => OpenJModel318.Base N
local notation "a" => algebraMap R S
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "hS" => CompletedAdditionCoefficient318.mapped_discriminant (S:=S) A B hD

/-- Actual Scheme-level associativity on the literal left-associated relative
triple after any coefficient extension, including arbitrary nilpotent bases.
It is obtained by the actual cartesian coefficient square and multiplication
comparison, not by reduced field-point testing on the changed base. -/
theorem associative : leftAssociate (a A) (a B) hS=rightAssociate (a A) (a B) hS := by
  let b:=first (a A) (a B) ≫ WeierstrassGluing318.structureMap (a A) (a B)
  let p:Points N S b:=⟨first (a A) (a B),rfl⟩
  let q:Points N S b:=⟨second (a A) (a B),(first_second_base (a A) (a B)).symm⟩
  let r:Points N S b:=⟨third (a A) (a B),(first_third_base (a A) (a B)).symm⟩
  have h12:pair N S b p q=pair12 (a A) (a B):=by
    apply pullback.hom_ext
    · rw [pair_fst,pair12_fst]
    · rw [pair_snd,pair12_snd]
  have h23:pair N S b q r=pair23 (a A) (a B):=by
    apply pullback.hom_ext
    · rw [pair_fst,pair23_fst]
    · rw [pair_snd,pair23_snd]
  have hl:pair N S b (sum N S b p q) r=leftPair (a A) (a B) hS:=by
    apply pullback.hom_ext
    · rw [pair_fst,leftPair_fst]
      change pair N S b p q ≫ _=_
      rw [h12]
    · rw [pair_snd,leftPair_snd]
  have hr:pair N S b p (sum N S b q r)=rightPair (a A) (a B) hS:=by
    apply pullback.hom_ext
    · rw [pair_fst,rightPair_fst]
    · rw [pair_snd,rightPair_snd]
      change pair N S b q r ≫ _=_
      rw [h23]
  have h:=congrArg Subtype.val (CoefficientPointGroup318.sum_assoc N S b p q r)
  change pair N S b (sum N S b p q) r ≫ CompletedAddition318.addition (a A) (a B) hS=
    pair N S b p (sum N S b q r) ≫ CompletedAddition318.addition (a A) (a B) hS at h
  rw [hl,hr] at h
  exact h
end CoefficientGroupAssociativity318
