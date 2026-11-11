module
public import NormalizedStructureTrace318
public import CompletedCharacterOpenTrace318
public import FifthOpenTrace318

public section
noncomputable section
namespace ActualQuotientSheafRetraction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open StructureAdditiveSheaf318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing original complementary regular-function trace, lifted to sheaves. -/
@[expose] def characterTrace (i : Fin 4) :
    pushed (CompletedCharacterGlobal318.completedMap i) ⟶
      sheaf (CompletedCharacterSchemeMaps318.Target i) :=
  ⟨CompletedCharacterOpenTrace318.transfer i⟩

/-- The existing original fifth regular-function trace, lifted to sheaves. -/
@[expose] def fifthTrace : pushed FifthCompletedGlobal318.map ⟶
    sheaf FifthCompletedGlobal318.Target := ⟨FifthOpenTrace318.transfer⟩

@[expose] def characterRetraction (i : Fin 4) :
    pushed (CompletedCharacterGlobal318.completedMap i) ⟶
      sheaf (CompletedCharacterSchemeMaps318.Target i) :=
  NormalizedStructureTrace318.retraction _
    (WeierstrassGluing318.structureMap (publishedA i) (publishedB i)) (characterTrace i)

@[expose] def fifthRetraction : pushed FifthCompletedGlobal318.map ⟶
    sheaf FifthCompletedGlobal318.Target :=
  NormalizedStructureTrace318.retraction _
    (WeierstrassGluing318.structureMap FifthCharacterShortPolynomial318.A
      FifthCharacterShortPolynomial318.B) fifthTrace

theorem character_split (i : Fin 4) :
    pullback (CompletedCharacterGlobal318.completedMap i) ≫ characterRetraction i =
      𝟙 (sheaf (CompletedCharacterSchemeMaps318.Target i)) :=
  NormalizedStructureTrace318.pullback_retraction _ _ _
    (CompletedCharacterOpenTrace318.trace_pullback i)

theorem fifth_split : pullback FifthCompletedGlobal318.map ≫ fifthRetraction =
    𝟙 (sheaf FifthCompletedGlobal318.Target) :=
  NormalizedStructureTrace318.pullback_retraction _ _ _ FifthOpenTrace318.trace_pullback

/-- Component formula retains the actual original trace and scalar exactly 1/8. -/
theorem character_component (i : Fin 4) (U : (CompletedCharacterSchemeMaps318.Target i).Opens)
    (s : Γ(ContactGlobalSmooth318.Model units, CompletedCharacterGlobal318.completedMap i ⁻¹ᵁ U)) :
    (characterRetraction i).hom.app (op U) s =
      NormalizedStructureTrace318.scalar
        (WeierstrassGluing318.structureMap (publishedA i) (publishedB i)) U (1/8) *
      CompletedCharacterOpenTrace318.trace i U s := rfl

theorem fifth_component (U : FifthCompletedGlobal318.Target.Opens)
    (s : Γ(ContactGlobalSmooth318.Model units, FifthCompletedGlobal318.map ⁻¹ᵁ U)) :
    fifthRetraction.hom.app (op U) s =
      NormalizedStructureTrace318.scalar
        (WeierstrassGluing318.structureMap FifthCharacterShortPolynomial318.A
          FifthCharacterShortPolynomial318.B) U (1/8) * FifthOpenTrace318.trace U s := rfl

end ActualQuotientSheafRetraction318
