module
public import LiteralSchemePointOperations318
public section
noncomputable section
namespace LiteralSchemePointAssociativity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralSchemePointOperations318 CompletedAdditionTriple318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {T:Scheme}
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "pE" => WeierstrassGluing318.structureMap A B
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
variable (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
@[expose] def tripleInput (p q r:Points N b) : T ⟶ triple A B :=
  pullback.lift (pair N b p q) r.val (by
    change pair N b p q ≫ pullback.fst _ _ ≫ pE=r.val ≫ pE
    rw [pair_fst_assoc,p.property,r.property])
@[reassoc] theorem tripleInput_pair12 (p q r:Points N b) :
    tripleInput N b p q r ≫ pair12 A B=pair N b p q := by simp [tripleInput,pair12]
@[reassoc] theorem tripleInput_third (p q r:Points N b) :
    tripleInput N b p q r ≫ third A B=r.val := by simp [tripleInput,third]
@[reassoc] theorem tripleInput_first (p q r:Points N b) :
    tripleInput N b p q r ≫ first A B=p.val := by
  rw [←pair12_fst,←Category.assoc,tripleInput_pair12,pair_fst]
@[reassoc] theorem tripleInput_second (p q r:Points N b) :
    tripleInput N b p q r ≫ second A B=q.val := by
  rw [←pair12_snd,←Category.assoc,tripleInput_pair12,pair_snd]
@[reassoc] theorem tripleInput_pair23 (p q r:Points N b) :
    tripleInput N b p q r ≫ pair23 A B=pair N b q r := by
  apply pullback.hom_ext
  · rw [Category.assoc,pair23_fst,tripleInput_second,pair_fst]
  · rw [Category.assoc,pair23_snd,tripleInput_third,pair_snd]
theorem leftPair_input (p q r:Points N b) :
    pair N b (sum N b p q) r=tripleInput N b p q r ≫ leftPair A B hD := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,leftPair_fst,←Category.assoc,tripleInput_pair12]
    rfl
  · rw [pair_snd,Category.assoc,leftPair_snd,tripleInput_third]
theorem rightPair_input (p q r:Points N b) :
    pair N b p (sum N b q r)=tripleInput N b p q r ≫ rightPair A B hD := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,rightPair_fst,tripleInput_first]
  · rw [pair_snd,Category.assoc,rightPair_snd,←Category.assoc,tripleInput_pair23]
    rfl
/-- Associativity on arbitrary test Schemes follows from the checked literal
Scheme-map equation, without any reducedness assumption on the test object. -/
theorem sum_assoc (p q r:Points N b) :
    sum N b (sum N b p q) r=sum N b p (sum N b q r) := by
  apply Subtype.ext
  change pair N b (sum N b p q) r ≫ CompletedAddition318.addition A B hD=
    pair N b p (sum N b q r) ≫ CompletedAddition318.addition A B hD
  calc
    _=tripleInput N b p q r ≫ leftAssociate A B hD := by
      rw [leftPair_input,Category.assoc,leftAssociate]
    _=tripleInput N b p q r ≫ rightAssociate A B hD :=
      congrArg (fun f=>tripleInput N b p q r ≫ f) (LiteralGroupAssociativity318.associative N)
    _=_ := by rw [rightPair_input,Category.assoc,rightAssociate]
end LiteralSchemePointAssociativity318
