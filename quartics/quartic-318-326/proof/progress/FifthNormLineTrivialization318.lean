module
public import FifthNormClutchedLine318
public import OpenClutchedTrivialization318
public import FifthNormCocycle318
public section
noncomputable section
namespace FifthNormLineTrivialization318
open AlgebraicGeometry CategoryTheory Opposite
open FifthCompletedGlobal318 FifthNormClutchedLine318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def cover:Bool→Target.Opens:=fun b=>if b then right else left
abbrev SourceUnits:=(StructureUnitsSheaf318.pushedUnits map).obj
abbrev TargetUnits:=(StructureUnitsSheaf318.units Target).obj
variable (b:∀i,SourceUnits.obj (op (cover i)))
@[expose] def sourceCoboundary:Γ(Model,map⁻¹ᵁoverlap)ˣ:=
  UnitTransitionCocycle318.coboundary SourceUnits cover b false true
@[expose] def coefficient (i:Bool):Γ(Target,cover i)ˣ:=
  FifthSheafNorm318.norm.hom.app (op (cover i)) (b i)
lemma target_coboundary:
    targetTransition (sourceCoboundary b)=
      UnitTransitionCocycle318.coboundary TargetUnits cover (coefficient b) false true:=
  FifthNormCocycle318.coboundary cover b false true
lemma target_compatible:
    Target.presheaf.map (homOfLE (show overlap≤left from inf_le_left)).op
        (coefficient b false).val=
      Target.presheaf.map (homOfLE (show overlap≤right from inf_le_right)).op
        (coefficient b true).val*(targetTransition (sourceCoboundary b)).val:=by
  let r₀:Γ(Target,overlap)ˣ:=Units.map
    (Target.presheaf.map (homOfLE (show overlap≤left from inf_le_left)).op).hom.toMonoidHom
    (coefficient b false)
  let r₁:Γ(Target,overlap)ˣ:=Units.map
    (Target.presheaf.map (homOfLE (show overlap≤right from inf_le_right)).op).hom.toMonoidHom
    (coefficient b true)
  have ht:=target_coboundary b
  change targetTransition (sourceCoboundary b)=r₀*r₁⁻¹ at ht
  have h:r₀=r₁*targetTransition (sourceCoboundary b):=by
    rw [ht]
    rw [←mul_assoc, mul_comm r₁ r₀, mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg Units.val h

/-- An actual O-module-sheaf isomorphism: the norm of a specified source
unit coboundary gives the trivial target line with its genuine local frames. -/
@[expose] def iso:ClutchedModule318.unit Target≅normLine (sourceCoboundary b):=
  OpenClutchedTrivialization318.iso left right (targetTransition (sourceCoboundary b))
    (coefficient b false) (coefficient b true) (target_compatible b) target_cover
/-- Original transition functions, not a Picard-class operation. -/
@[expose] def lineOfCocycle (c:FifthNormCocycle318.SourceCocycle cover):Target.Modules:=
  normLine (c.transition false true)
lemma lineOfCocycle_transition (c:FifthNormCocycle318.SourceCocycle cover):
    targetTransition (c.transition false true)=(FifthNormCocycle318.transfer c).transition false true:=rfl
end FifthNormLineTrivialization318
