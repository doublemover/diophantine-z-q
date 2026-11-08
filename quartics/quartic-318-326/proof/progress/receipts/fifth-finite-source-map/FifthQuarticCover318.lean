module
public import FifthBranchEquation318
public import FifthCharacterOrder318
public import Mathlib.AlgebraicGeometry.Cover.Open
public section
noncomputable section
namespace FifthQuarticCover318
open Polynomial AlgebraicGeometry
open FifthBranchEquation318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Quartic:=FifthCharacterOrder318.Order
@[expose] def parameter:Quartic:=algebraMap ℚ[X] Quartic X
@[expose] def branchDenominator:Quartic:=algebraMap ℚ[X] Quartic branchFactor
@[expose] def chartElement:Bool→Quartic
  | false=>parameter
  | true=>branchDenominator

theorem span_top:Ideal.span (Set.range chartElement)=⊤:=by
  let J:=Ideal.span (Set.range chartElement)
  have ht:parameter∈J:=Ideal.subset_span ⟨false,rfl⟩
  have hh:branchDenominator∈J:=Ideal.subset_span ⟨true,rfl⟩
  have he:=congrArg (algebraMap ℚ[X] Quartic) (Polynomial.X_mul_divX_add branchFactor)
  simp only [map_add,map_mul] at he
  have hc:algebraMap ℚ[X] Quartic (C (branchFactor.coeff 0))∈J:=by
    rw [eq_sub_of_add_eq' he]
    exact J.sub_mem hh (J.mul_mem_right _ ht)
  have hu:IsUnit (C (branchFactor.coeff 0):ℚ[X]):=by
    apply IsUnit.map C
    apply IsUnit.mk0
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using branchFactor_zero
  exact J.eq_top_of_isUnit_mem hc (hu.map (algebraMap ℚ[X] Quartic))

/-- Actual two principal opens covering the whole quartic affine scheme.
The second contains the branch t=y=0; neither chart is discarded. -/
@[expose] def cover:(Spec (CommRingCat.of Quartic)).OpenCover:=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R:=CommRingCat.of Quartic) chartElement span_top).openCover
end FifthQuarticCover318
