module
public import StructureUnitsSheaf318
public import CompletedCharacterOpenNorm318
public section
noncomputable section
namespace CompletedCharacterSheafNorm318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterTraceBasis318
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapDominant (i:Fin 4):IsDominant (completedMap i):=
  CompletedCharacterProper318.completedMap_dominant i
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
/-- A genuine morphism between the actual sheaves of units for each
original completed character quotient. -/
@[expose] def norm (i:Fin 4):StructureUnitsSheaf318.pushedUnits (completedMap i)⟶
    StructureUnitsSheaf318.units (Target i):=
  StructureUnitsSheaf318.norm (completedMap i) (hasBasis i)
@[expose] def pullback (i:Fin 4):StructureUnitsSheaf318.units (Target i)⟶
    StructureUnitsSheaf318.pushedUnits (completedMap i):=
  ⟨Functor.whiskerRight (completedMap i).c OpenUnitNorm318.unitsFunctor⟩
@[expose] def eighthPower (i:Fin 4):StructureUnitsSheaf318.units (Target i)⟶
    StructureUnitsSheaf318.units (Target i):=
  ⟨{app U:=CommGrpCat.ofHom (powMonoidHom 8)
    naturality U V j:=by
      apply CommGrpCat.ext
      intro s
      exact (map_pow _ s 8).symm}⟩
/-- Pullback followed by the genuine norm equals the actual eighth-power
endomorphism of the entire target units sheaf. -/
theorem pullback_norm (i:Fin 4):pullback i≫norm i=eighthPower i:=by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommGrpCat.ext
  intro s
  exact CompletedCharacterOpenNorm318.unit_pullback i U.unop s
lemma original_value (i:Fin 4) (U:(Target i).Opens) (s:Γ(Model,completedMap i⁻¹ᵁU)ˣ):
    Units.val (α:=Γ(Target i,U)) ((norm i).hom.app (op U) s)=
      CompletedCharacterOpenNorm318.norm i U (s:Γ(Model,completedMap i⁻¹ᵁU)):=rfl
end CompletedCharacterSheafNorm318
