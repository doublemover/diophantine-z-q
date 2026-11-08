module
public import FiniteFlatGenericRank318
public import CompletedCharacterDegree318
public import CompletedCharacterFlat318
public section
noncomputable section
namespace CompletedCharacterRank318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral : IsIntegral (ContactProjectiveModel318.model units) :=
  ContactProjectiveModel318.model_integral units
local instance targetIntegral (i : Fin 4) : IsIntegral (Target i) :=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapDominant (i : Fin 4) : IsDominant (completedMap i) :=
  CompletedCharacterProper318.completedMap_dominant i
local instance mapFinite (i : Fin 4) : IsFinite (completedMap i) :=
  CompletedCharacterFinite318.completedMap_finite i
local instance mapFlat (i : Fin 4) : Flat (completedMap i) :=
  CompletedCharacterFlat318.completedMap_flat i

/-- The original whole completed character map has actual Scheme rank eight
at every target point, including every finite branch point and infinity.
The generic degree uses the original actual generic-stalk pullback algebra. -/
theorem completedMap_rank_eight (i : Fin 4) (y : Target i) :
    (completedMap i).finrank y = 8 := by
  letI := CompletedCharacterDegree318.pullbackAlgebra i
  exact (FiniteFlatGenericRank318.finrank_eq_generic_degree (completedMap i) y).trans
    (CompletedCharacterDegree318.actual_generic_degree_eight i)

/-- Finite flat degree eight and surjectivity refer to the unchanged actual map. -/
theorem finite_flat_rank_eight_surjective (i : Fin 4) :
    IsFinite (completedMap i) ∧ Flat (completedMap i) ∧
      Surjective (completedMap i) ∧ ∀ y : Target i, (completedMap i).finrank y = 8 :=
  ⟨inferInstance, inferInstance, CompletedCharacterProper318.completedMap_surjective i,
    completedMap_rank_eight i⟩
end CompletedCharacterRank318
