module
public import FifthFormGlobalRestriction318
public section
noncomputable section
namespace FifthFormCommonOpen318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthFormLocalCoefficients318 ContactOverlapIntrinsic318
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] toOpen_open
@[expose] def weighted (i:Fin 4) (a:O):Γ(M,embedding units ''ᵁ ⊤):=
  ScaledGlobalSectionRestriction318.scaled M (embedding units) a
    (ContactCharacterDifferentials318.differential i)

theorem weighted_eq_section (i:Fin 4) (a:O):weighted i a=
    IntrinsicChartSections318.sectionMap (embedding units)
      (ContactIntrinsicDifferentials318.structureMap units) (over_Q units) (a • form i):=by
  unfold weighted ScaledGlobalSectionRestriction318.scaled
  rw [global_restrict,IntrinsicChartSections318.section_smul]
  rfl

end FifthFormCommonOpen318
