module
public import StructureUnitsSheaf318
public import FifthOpenNorm318
public section
noncomputable section
namespace FifthSheafNorm318
open AlgebraicGeometry CategoryTheory Opposite
open FifthCompletedGlobal318
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Model:=FifthOpenNorm318.Model
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral SourceTwistArithmetic318.units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance mapDominant:IsDominant map:=FifthCompletedProper318.dominant
/-- Genuine norm morphism between actual unit sheaves of the completed fifth map. -/
@[expose] def norm:StructureUnitsSheaf318.pushedUnits map⟶StructureUnitsSheaf318.units Target:=
  StructureUnitsSheaf318.norm map FifthTargetNormalBasis318.hasBasis
/-- The original Scheme pullback on invertible regular functions. -/
@[expose] def pullback:StructureUnitsSheaf318.units Target⟶StructureUnitsSheaf318.pushedUnits map:=
  ⟨Functor.whiskerRight map.c OpenUnitNorm318.unitsFunctor⟩
/-- The eighth-power endomorphism of the actual target units sheaf. -/
@[expose] def eighthPower:StructureUnitsSheaf318.units Target⟶StructureUnitsSheaf318.units Target:=
  ⟨{app U:=CommGrpCat.ofHom (powMonoidHom 8)
    naturality U V i:=by
      apply CommGrpCat.ext
      intro s
      exact (map_pow _ s 8).symm}⟩
lemma pullback_norm:pullback≫norm=eighthPower:=by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommGrpCat.ext
  intro s
  exact FifthOpenNorm318.unit_pullback U.unop s
lemma norm_original_value (U:Target.Opens) (s:Γ(Model,map⁻¹ᵁU)ˣ):
    Units.val (α:=Γ(Target,U)) (norm.hom.app (op U) s)=
      FifthOpenNorm318.norm U (s:Γ(Model,map⁻¹ᵁU)):=rfl
end FifthSheafNorm318
