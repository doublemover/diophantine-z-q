module
public import FifthCompletedFlat318
public import FiniteFlatGenericRank318
public section
noncomputable section
namespace FifthCompletedRank318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral (ContactGlobalSmooth318.Model units):=
  ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance mapDominant:IsDominant map:=FifthCompletedProper318.dominant
local instance mapFlat:Flat map:=FifthCompletedFlat318.flat
/-- Rank eight at every actual target point; its generic scalar action is the
actual fifth morphism's pullback already identified with the original character. -/
theorem rank_eight (y:Target):map.finrank y=8:=by
  rw [FiniteFlatGenericRank318.finrank_eq_generic_degree]
  exact FifthCompletedDegree318.actual_generic_degree_eight
theorem finite_flat_surjective_rank_eight:
    IsFinite map∧Flat map∧Surjective map∧∀y:Target,map.finrank y=8:=
  ⟨FifthCompletedFinite318.finite,FifthCompletedFlat318.flat,
    FifthCompletedProper318.surjective,rank_eight⟩
end FifthCompletedRank318
