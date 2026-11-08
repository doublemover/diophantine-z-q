module
public import StructuralConstantPullback318
public import ActualTargetRationalInvariants318
public section
noncomputable section
namespace ActualQuotientConstantPullback318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev p := ContactIntrinsicDifferentials318.structureMap units
/-- The one unchanged structural rational-constant map on the original source. -/
@[expose] def sourceConstant : ℚ →+* Γ(ContactGlobalSmooth318.Model units, ⊤) :=
  StructuralConstantPullback318.constant p
lemma character_constant (i : Fin 4) (a : ℚ) :
    (CompletedCharacterGlobal318.completedMap i).appTop
      (ActualTargetRationalInvariants318.characterConstant i a) = sourceConstant a :=
  StructuralConstantPullback318.app_constant _ p _ (CompletedCharacterGlobal318.over_Q i) a
lemma fifth_constant (a : ℚ) :
    FifthCompletedGlobal318.map.appTop (ActualTargetRationalInvariants318.fifthConstant a) =
      sourceConstant a :=
  StructuralConstantPullback318.app_constant _ p _ FifthCompletedGlobal318.over_Q a
/-- Exact scalar-one normalization for each original complementary invariant. -/
theorem character_invariant_multiple (i : Fin 4) (a : ℚ) :
    IntrinsicDifferentialPullback318.globalSection (CompletedCharacterGlobal318.completedMap i)
      p (WeierstrassGluing318.structureMap (publishedA i) (publishedB i))
      (CompletedCharacterGlobal318.over_Q i)
      (ActualTargetRationalInvariants318.characterConstant i a • ContactCharacterDifferentials318.invariant i) =
      sourceConstant a • ContactCharacterDifferentials318.differential i :=
  StructuralConstantPullback318.globalSection_constant_smul _ p _
    (CompletedCharacterGlobal318.over_Q i) a (ContactCharacterDifferentials318.invariant i)
/-- The fifth original invariant has the same structural-constant compatibility. -/
theorem fifth_invariant_multiple (a : ℚ) :
    IntrinsicDifferentialPullback318.globalSection FifthCompletedGlobal318.map p
      (WeierstrassGluing318.structureMap FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B)
      FifthCompletedGlobal318.over_Q
      (ActualTargetRationalInvariants318.fifthConstant a • FifthActualDifferential318.invariant) =
      sourceConstant a • FifthActualDifferential318.differential :=
  StructuralConstantPullback318.globalSection_constant_smul _ p _ FifthCompletedGlobal318.over_Q a
    FifthActualDifferential318.invariant
end ActualQuotientConstantPullback318
