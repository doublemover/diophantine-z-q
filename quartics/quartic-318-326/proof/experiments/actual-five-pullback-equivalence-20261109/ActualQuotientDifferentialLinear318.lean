module
public import ActualFiveDifferentialBasis318
public import CharacterTargetDifferentialInvariants318
public import FifthTargetDifferentialInvariants318

public section
noncomputable section
namespace ActualQuotientDifferentialLinear318
open AlgebraicGeometry SourceTwistArithmetic318
open ActualFiveRationalIndependent318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] rationalModule

abbrev CharacterSpace (i : Fin 4) :=
  Γ(CharacterTargetDifferentialInvariants318.N i, ⊤)
abbrev FifthSpace := Γ(FifthTargetDifferentialInvariants318.N, ⊤)

/-- The target rational action is restriction along its original structure map. -/
@[expose, instance_reducible] def characterModule (i : Fin 4) : Module ℚ (CharacterSpace i) :=
  Module.compHom (CharacterSpace i) (ActualTargetRationalInvariants318.characterConstant i)
@[expose, instance_reducible] def fifthModule : Module ℚ FifthSpace :=
  Module.compHom FifthSpace ActualTargetRationalInvariants318.fifthConstant
attribute [local instance] characterModule fifthModule

/-- Q-linearity of the actual whole-scheme complementary differential pullback. -/
@[expose] def characterPullback (i : Fin 4) : CharacterSpace i →ₗ[ℚ] G where
  toFun := CharacterTargetDifferentialInvariants318.pullback i
  map_add' := (CharacterTargetDifferentialInvariants318.pullback i).map_add
  map_smul' a s :=
    StructuralConstantPullback318.globalSection_constant_smul _ _ _
      (CompletedCharacterGlobal318.over_Q i) a s

/-- Q-linearity of the actual whole-scheme fifth differential pullback. -/
@[expose] def fifthPullback : FifthSpace →ₗ[ℚ] G where
  toFun := FifthTargetDifferentialInvariants318.pullback
  map_add' := FifthTargetDifferentialInvariants318.pullback.map_add
  map_smul' a s :=
    StructuralConstantPullback318.globalSection_constant_smul _ _ _
      FifthCompletedGlobal318.over_Q a s

/-- The original normalized invariant is a basis of each actual target space. -/
@[expose] def characterFrame (i : Fin 4) : ℚ ≃ₗ[ℚ] CharacterSpace i :=
  LinearEquiv.ofBijective
    { toFun := fun a => a • (show CharacterSpace i from ContactCharacterDifferentials318.invariant i)
      map_add' := fun a b => add_smul a b _
      map_smul' := fun a b => mul_smul a b _ }
    (ActualTargetRationalInvariants318.character_bijective i)

@[expose] def fifthFrame : ℚ ≃ₗ[ℚ] FifthSpace :=
  LinearEquiv.ofBijective
    { toFun := fun a => a • (show FifthSpace from FifthActualDifferential318.invariant)
      map_add' := fun a b => add_smul a b _
      map_smul' := fun a b => mul_smul a b _ }
    ActualTargetRationalInvariants318.fifth_bijective

abbrev Index := Option (Fin 4)
/-- Five actual completed quotient differential spaces, including the fifth. -/
abbrev TargetSpace : Index → Type
  | none => FifthSpace
  | some i => CharacterSpace i

instance targetAddCommGroup (i : Index) : AddCommGroup (TargetSpace i) := by
  cases i <;> exact inferInstance
@[expose, instance_reducible] def targetModule (i : Index) : Module ℚ (TargetSpace i) := by
  cases i <;> exact inferInstance
attribute [local instance] targetModule

@[expose] def frame (i : Index) : ℚ ≃ₗ[ℚ] TargetSpace i :=
  match i with
  | none => fifthFrame
  | some i => characterFrame i

@[expose] def pullback (i : Index) : TargetSpace i →ₗ[ℚ] G :=
  match i with
  | none => fifthPullback
  | some i => characterPullback i

/-- The generator comparison has scalar exactly one in all five components. -/
theorem pullback_frame (i : Index) (a : ℚ) :
    pullback i (frame i a) = a • differential i := by
  cases i with
  | none => exact ActualQuotientConstantPullback318.fifth_invariant_multiple a
  | some i => exact ActualQuotientConstantPullback318.character_invariant_multiple i a

end ActualQuotientDifferentialLinear318
