module
public import PELOriginalCharacterNativeDegree318
public import PELOriginalWholeCharacterFlat318
public import FiniteFlatGenericRank318
public section
noncomputable section
namespace PELOriginalCharacterNativeRank318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral:IsIntegral (FourRootGluedScheme318.scheme branches):=
  FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance mapDominant (i:Fin 4):IsDominant (morphism i):=
  PELOriginalWholeCharacterProper318.dominant i
local instance mapFinite (i:Fin 4):IsFinite (morphism i):=
  PELOriginalWholeCharacterFinite318.finite i
local instance mapFlat (i:Fin 4):Flat (morphism i):=
  PELOriginalWholeCharacterFlat318.flat i

/-- Actual Scheme rank eight at EVERY target point, including every
finite branch point and infinity. The generic scalar action is the native
pullback of this same morphism, verified in the preceding field square. -/
theorem rank_eight (i:Fin 4) (y:Curve i):(morphism i).finrank y=8:=by
  letI:=PELOriginalCharacterNativeDegree318.pullbackAlgebra i
  exact (FiniteFlatGenericRank318.finrank_eq_generic_degree (morphism i) y).trans
    (PELOriginalCharacterNativeDegree318.actual_generic_degree_eight i)

/-- One unchanged whole original character map carries all properties. -/
theorem finite_flat_rank_eight_surjective (i:Fin 4):
    IsFinite (morphism i) ∧ Flat (morphism i) ∧ Surjective (morphism i) ∧
      ∀y:Curve i,(morphism i).finrank y=8:=
  ⟨inferInstance,inferInstance,PELOriginalWholeCharacterProper318.surjective i,rank_eight i⟩
end PELOriginalCharacterNativeRank318
