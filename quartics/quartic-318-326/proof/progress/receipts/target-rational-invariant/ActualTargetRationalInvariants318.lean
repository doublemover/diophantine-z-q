module
public import IntrinsicConstantInvariantGenerator318
public import ContactCharacterDifferentials318
public import FifthActualDifferential318
public section
noncomputable section
namespace ActualTargetRationalInvariants318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Literal rational constants on each of the four original elliptic targets. -/
@[expose] def characterConstant (i : Fin 4) : ℚ →+* Γ(CompletedCharacterSchemeMaps318.Target i, ⊤) :=
  IntrinsicConstantInvariantGenerator318.constant (publishedA i) (publishedB i)
theorem character_bijective (i : Fin 4) :
    Function.Bijective (fun a : ℚ => characterConstant i a • ContactCharacterDifferentials318.invariant i) :=
  IntrinsicConstantInvariantGenerator318.bijective (publishedA i) (publishedB i)
    (ContactCharacterDifferentials318.discriminantUnit i)
theorem character_unique (i : Fin 4)
    (s : Γ(FamilyIntrinsicDifferentials318.familyOmega (publishedA i) (publishedB i), ⊤)) :
    ∃! a : ℚ, characterConstant i a • ContactCharacterDifferentials318.invariant i = s :=
  IntrinsicConstantInvariantGenerator318.existsUnique (publishedA i) (publishedB i)
    (ContactCharacterDifferentials318.discriminantUnit i) s
/-- Literal rational constants on the actual fifth elliptic target. -/
@[expose] def fifthConstant : ℚ →+* Γ(FifthCompletedGlobal318.Target, ⊤) :=
  IntrinsicConstantInvariantGenerator318.constant FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
theorem fifth_bijective :
    Function.Bijective (fun a : ℚ => fifthConstant a • FifthActualDifferential318.invariant) :=
  IntrinsicConstantInvariantGenerator318.bijective FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
    FifthCharacterShortPolynomial318.discriminant_unit
theorem fifth_unique
    (s : Γ(FamilyIntrinsicDifferentials318.familyOmega FifthCharacterShortPolynomial318.A
      FifthCharacterShortPolynomial318.B, ⊤)) :
    ∃! a : ℚ, fifthConstant a • FifthActualDifferential318.invariant = s :=
  IntrinsicConstantInvariantGenerator318.existsUnique FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
    FifthCharacterShortPolynomial318.discriminant_unit s
end ActualTargetRationalInvariants318
