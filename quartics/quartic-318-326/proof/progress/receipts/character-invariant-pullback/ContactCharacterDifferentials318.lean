module
public import IntrinsicDifferentialPullback318
public import IntrinsicGlobalFrame318
public import ContactIntrinsicDifferentials318
public import CompletedCharacterGlobal318
public section
noncomputable section
namespace ContactCharacterDifferentials318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

@[expose] def discriminantUnit (i:Fin 4) :
    IsUnit (-16*(4*(publishedA i)^3+27*(publishedB i)^2)) :=
  isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (published_nonsingular i))

/-- The actual global elliptic invariant differential on the exact completed
published target, with its established dx/(2y) normalization. -/
@[expose] def invariant (i:Fin 4) :=
  IntrinsicGlobalFrame318.invariant (publishedA i) (publishedB i) (discriminantUnit i)

/-- The canonical differential map for the whole completed character map. -/
@[expose] def map (i:Fin 4) :=
  IntrinsicDifferentialPullback318.map (CompletedCharacterGlobal318.completedMap i)
    (ContactIntrinsicDifferentials318.structureMap units)
    (WeierstrassGluing318.structureMap (publishedA i) (publishedB i))
    (CompletedCharacterGlobal318.over_Q i)

/-- The genuine pullback differential morphism, not an assigned function-field map. -/
@[expose] def pullbackMap (i:Fin 4) :=
  IntrinsicDifferentialPullback318.pullbackMap (CompletedCharacterGlobal318.completedMap i)
    (ContactIntrinsicDifferentials318.structureMap units)
    (WeierstrassGluing318.structureMap (publishedA i) (publishedB i))
    (CompletedCharacterGlobal318.over_Q i)

/-- Four actual global intrinsic differentials on the complete contact source. -/
@[expose] def differential (i:Fin 4) : Γ(ContactIntrinsicDifferentials318.omega units,⊤) :=
  IntrinsicDifferentialPullback318.globalSection (CompletedCharacterGlobal318.completedMap i)
    (ContactIntrinsicDifferentials318.structureMap units)
    (WeierstrassGluing318.structureMap (publishedA i) (publishedB i))
    (CompletedCharacterGlobal318.over_Q i) (invariant i)

theorem section_eq (i:Fin 4) : differential i=(map i).val.app (op ⊤) (invariant i) := rfl

/-- Exact universal-derivative normalization on every open of the completed target. -/
theorem map_D (i:Fin 4) (U:(CompletedCharacterSchemeMaps318.Target i).Opens)
    (s:Γ(CompletedCharacterSchemeMaps318.Target i,U)) :
    (map i).val.app (op U)
      ((FamilyIntrinsicDifferentials318.familyD (publishedA i) (publishedB i)).d s)=
        (ContactIntrinsicDifferentials318.derivation units).d
          ((CompletedCharacterGlobal318.completedMap i).app U s) :=
  IntrinsicDifferentialPullback318.map_D _ _ _ _ U s
end ContactCharacterDifferentials318
