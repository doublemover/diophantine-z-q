module
public import FifthPrincipalNeighborhood318
public import FiniteFreeGenericTransfer318
public import FifthOpenTrace318
public import FifthOpenNorm318
public section
noncomputable section
namespace FifthLocalMatrixTransfer318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance mapDominant:IsDominant map:=FifthCompletedProper318.dominant
local instance sectionAlgebra (U:Target.Opens):Algebra Γ(Target,U) Γ(Model,map⁻¹ᵁU):=
  (map.app U).hom.toAlgebra
variable (U:Target.Opens) (hU:IsAffineOpen U) [Nonempty U]
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
include hU
/-- The existing all-open regular trace equals the trace of multiplication
in any actual finite basis on this affine neighborhood. -/
lemma trace_eq (bs:Module.Basis ι Γ(Target,U) Γ(Model,map⁻¹ᵁU)) (s:Γ(Model,map⁻¹ᵁU)):
    Matrix.trace (Algebra.leftMulMatrix bs s)=FifthOpenTrace318.trace U s:=by
  letI:Nonempty (map⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty map U
  apply Target.germToFunctionField_injective U
  exact (FiniteFreeGenericTransfer318.trace_germ map U hU bs s).trans
    (FifthOpenTrace318.original_generic_trace U s).symm
/-- The existing all-open regular norm equals the determinant of the same
actual multiplication matrix. No chosen global free basis is asserted. -/
lemma norm_eq (bs:Module.Basis ι Γ(Target,U) Γ(Model,map⁻¹ᵁU)) (s:Γ(Model,map⁻¹ᵁU)):
    Matrix.det (Algebra.leftMulMatrix bs s)=FifthOpenNorm318.norm U s:=by
  letI:Nonempty (map⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty map U
  apply Target.germToFunctionField_injective U
  exact (FiniteFreeGenericTransfer318.norm_germ map U hU bs s).trans
    (FifthOpenNorm318.original_generic_norm U s).symm
omit hU in
/-- A genuine cover by rank-eight free pushforward modules, with both actual
matrix transfers identified with the original regular-function transfers. -/
lemma local_control (x:Target):
    ∃(b:Bool)(r:Γ(Target,chartOpen b)),x∈Target.basicOpen r ∧
      ∃bs:Module.Basis (Fin 8) Γ(Target,Target.basicOpen r) Γ(Model,map⁻¹ᵁTarget.basicOpen r),
        ∀s:Γ(Model,map⁻¹ᵁTarget.basicOpen r),
          Matrix.trace (Algebra.leftMulMatrix bs s)=FifthOpenTrace318.trace (Target.basicOpen r) s ∧
          Matrix.det (Algebra.leftMulMatrix bs s)=FifthOpenNorm318.norm (Target.basicOpen r) s:=by
  obtain ⟨b,r,hx,⟨bs⟩⟩:=FifthPrincipalNeighborhood318.cover x
  letI:Nonempty (Target.basicOpen r):=⟨⟨x,hx⟩⟩
  refine ⟨b,r,hx,bs,fun s=>⟨?_,?_⟩⟩
  · exact trace_eq (Target.basicOpen r) ((chart_affine b).basicOpen r) bs s
  · exact norm_eq (Target.basicOpen r) ((chart_affine b).basicOpen r) bs s
end FifthLocalMatrixTransfer318
