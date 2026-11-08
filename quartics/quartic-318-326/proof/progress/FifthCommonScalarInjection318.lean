module
public import IntrinsicChartScalarInjection318
public import FifthActualDifferentialRestriction318
public section
noncomputable section
namespace FifthCommonScalarInjection318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthOverlapCoordinates318 FifthOverlapDifferentialEquation318 FifthCharacterShortPolynomial318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma coefficient_unit:IsUnit coefficient:=by
  have h:IsUnit ((2*algebraMap ℚ O (yScale:ℚ)*w)*coefficient):=by
    rw [normalized_equation]
    exact ((xScale.isUnit).map (algebraMap ℚ O)).neg
  exact isUnit_of_mul_isUnit_right h
/-- The actual fifth pullback generates on the entire unbranched common
open, so multiplication by it detects equality of actual scalar sections. -/
theorem injective:Function.Injective (fun a:Γ(ContactGlobalSmooth318.Model units,
    ContactOverlapIntrinsic318.embedding units ''ᵁ ⊤)=>a •
      (ContactIntrinsicDifferentials318.omega units).presheaf.map
        (homOfLE (show ContactOverlapIntrinsic318.embedding units ''ᵁ ⊤≤⊤ from le_top)).op
          FifthActualDifferential318.differential):=by
  rw [←FifthActualDifferentialRestriction318.restrict]
  exact IntrinsicChartScalarInjection318.injective (ContactOverlapIntrinsic318.embedding units)
    (ContactIntrinsicDifferentials318.structureMap units) (ContactOverlapIntrinsic318.over_Q units)
    (ContactUnbranchedDifferentialFrame318.frame units) pulled coefficient_unit
end FifthCommonScalarInjection318
