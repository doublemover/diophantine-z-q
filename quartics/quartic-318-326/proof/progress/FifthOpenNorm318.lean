module
public import OpenUnitNorm318
public import FifthTargetNormalBasis318
public section
noncomputable section
namespace FifthOpenNorm318
open AlgebraicGeometry CategoryTheory Opposite
open FifthCompletedGlobal318
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Model:=FifthChartNorm318.Model
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral SourceTwistArithmetic318.units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance mapDominant:IsDominant map:=FifthCompletedProper318.dominant
/-- Actual fifth quotient norm on every target open. -/
@[expose] def norm (U:Target.Opens):Γ(Model,map⁻¹ᵁU)→*Γ(Target,U):=
  OpenDominantNorm318.norm map FifthTargetNormalBasis318.hasBasis U
lemma restrict {U V:Target.Opens} (i:U⟶V) (s:Γ(Model,map⁻¹ᵁV)):
    Target.presheaf.map i.op (norm V s)=
      norm U (Model.presheaf.map (homOfLE (map.preimage_mono i.le)).op s):=
  OpenDominantNorm318.restrict map FifthTargetNormalBasis318.hasBasis i s
lemma original_generic_norm (U:Target.Opens) [Nonempty U] (s:Γ(Model,map⁻¹ᵁU)):
    letI:Nonempty (map⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty map U
    Target.germToFunctionField U (norm U s)=
      FifthGenericNorm318.norm (Model.germToFunctionField (map⁻¹ᵁU) s):=
  OpenDominantNorm318.norm_embedding map FifthTargetNormalBasis318.hasBasis U s
lemma pullback (U:Target.Opens) (s:Γ(Target,U)):
    norm U (map.app U s)=s^8:=by
  change OpenDominantNorm318.norm map FifthTargetNormalBasis318.hasBasis U (map.app U s)=_
  simpa only [FifthCompletedDegree318.actual_generic_degree_eight] using
    OpenDominantNorm318.pullback map FifthTargetNormalBasis318.hasBasis U s
lemma chart_eq (b:Bool):norm (FifthChartNorm318.chartOpen b)=FifthChartNorm318.norm b:=by
  letI:=FifthChartNorm318.chart_nonempty b
  letI:=FifthChartNorm318.chart_normal b
  exact OpenDominantNorm318.affine_eq map FifthTargetNormalBasis318.hasBasis _
    (FifthChartNorm318.chart_affine b)
/-- The actual all-open natural transformation on invertible regular functions. -/
@[expose] def unitNorm:OpenUnitNorm318.sourceUnits map⟶OpenUnitNorm318.targetUnits (Y:=Target):=
  OpenUnitNorm318.norm map FifthTargetNormalBasis318.hasBasis
lemma unit_pullback (U:Target.Opens) (s:Γ(Target,U)ˣ):
    unitNorm.app (op U) (Units.map (map.app U).hom.toMonoidHom s)=s^8:=by
  change (OpenUnitNorm318.norm map FifthTargetNormalBasis318.hasBasis).app (op U) _=_
  simpa only [FifthCompletedDegree318.actual_generic_degree_eight] using
    OpenUnitNorm318.pullback map FifthTargetNormalBasis318.hasBasis U s
end FifthOpenNorm318
