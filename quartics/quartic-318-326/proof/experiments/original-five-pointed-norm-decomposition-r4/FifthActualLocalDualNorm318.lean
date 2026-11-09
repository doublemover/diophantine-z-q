module
public import OriginalFiniteFreeDualTransfer318
public import FifthLocalMatrixTransfer318
public section
noncomputable section
namespace FifthActualLocalDualNorm318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral : IsIntegral Model := ContactProjectiveModel318.model_integral units
local instance targetIntegral : IsIntegral Target := FifthCompletedProper318.target_proper_integral.2
local instance mapFinite : IsFinite map := FifthCompletedFinite318.finite
local instance mapDominant : IsDominant map := FifthCompletedProper318.dominant
local instance sectionAlgebra (U : Target.Opens) : Algebra Γ(Target,U) Γ(Model,map ⁻¹ᵁ U) :=
  (map.app U).hom.toAlgebra
local instance dualSectionAlgebra (U : Target.Opens) :
    Algebra (DualNumber Γ(Target,U)) (DualNumber Γ(Model,map ⁻¹ᵁ U)) :=
  OriginalDualAlgebraNormTrace318.actualAlgebra Γ(Target,U) Γ(Model,map ⁻¹ᵁ U)
/-- Every point of the ACTUAL fifth target, including all branch and infinity
points, has an original rank-eight section basis on its ENTIRE inverse image.
There the dual determinant norm extends the OLD norm and differentiates to
the OLD trace on every original section. No global nonreduced norm is assumed. -/
lemma local_control (x : Target) :
    ∃ (b : Bool) (r : Γ(Target,chartOpen b)), x ∈ Target.basicOpen r ∧
      ∃ bs : Module.Basis (Fin 8) Γ(Target,Target.basicOpen r) Γ(Model,map ⁻¹ᵁ Target.basicOpen r),
        ∀ s : Γ(Model,map ⁻¹ᵁ Target.basicOpen r),
          Algebra.norm (DualNumber Γ(Target,Target.basicOpen r))
            (TrivSqZeroExt.inl s : DualNumber Γ(Model,map ⁻¹ᵁ Target.basicOpen r)) =
              TrivSqZeroExt.inl (FifthOpenNorm318.norm (Target.basicOpen r) s) ∧
          Units.map (Algebra.norm (DualNumber Γ(Target,Target.basicOpen r)))
            (SquareZeroUnit318.unit Γ(Model,map ⁻¹ᵁ Target.basicOpen r) s) =
              SquareZeroUnit318.unit Γ(Target,Target.basicOpen r)
                (FifthOpenTrace318.trace (Target.basicOpen r) s) := by
  obtain ⟨b,r,hx,⟨bs⟩⟩ := FifthPrincipalNeighborhood318.cover x
  letI : Nonempty (Target.basicOpen r) := ⟨⟨x,hx⟩⟩
  refine ⟨b,r,hx,bs,fun s => ⟨?_,?_⟩⟩
  · exact OriginalFiniteFreeDualTransfer318.norm_coefficient map FifthTargetNormalBasis318.hasBasis
      (Target.basicOpen r) ((chart_affine b).basicOpen r) bs s
  · exact OriginalFiniteFreeDualTransfer318.norm_unit map FifthTargetNormalBasis318.hasBasis
      FifthChartTrace318.generic_finite (Target.basicOpen r) ((chart_affine b).basicOpen r) bs s
end FifthActualLocalDualNorm318
