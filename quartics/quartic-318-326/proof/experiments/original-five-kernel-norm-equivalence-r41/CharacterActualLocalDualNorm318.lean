module
public import CharacterActualPrincipalBasis318
public import CompletedCharacterOpenNorm318
public import CompletedCharacterOpenTrace318
public section
noncomputable section
namespace CharacterActualLocalDualNorm318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterTraceBasis318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral : IsIntegral Model := ContactProjectiveModel318.model_integral units
local instance targetIntegral (i : Fin 4) : IsIntegral (Target i) :=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapFinite (i : Fin 4) : IsFinite (completedMap i) := CompletedCharacterFinite318.completedMap_finite i
local instance mapDominant (i : Fin 4) : IsDominant (completedMap i) := CompletedCharacterProper318.completedMap_dominant i
local instance sectionAlgebra (i : Fin 4) (U : (Target i).Opens) : Algebra Γ(Target i,U) Γ(Model,completedMap i ⁻¹ᵁ U) :=
  ((completedMap i).app U).hom.toAlgebra
local instance dualSectionAlgebra (i : Fin 4) (U : (Target i).Opens) :
    Algebra (DualNumber Γ(Target i,U)) (DualNumber Γ(Model,completedMap i ⁻¹ᵁ U)) :=
  OriginalDualAlgebraNormTrace318.actualAlgebra Γ(Target i,U) Γ(Model,completedMap i ⁻¹ᵁ U)
/-- For ALL four original quotient maps and EVERY actual target point, the
same original rank-eight local section algebra has a genuine dual determinant
norm extending the old norm and differentiating to the old trace. -/
lemma local_control (i : Fin 4) (x : Target i) :
    ∃ (b : Bool) (r : Γ(Target i,chartOpen i b)), x ∈ (Target i).basicOpen r ∧
      ∃ bs : Module.Basis (Fin 8) Γ(Target i,(Target i).basicOpen r)
          Γ(Model,completedMap i ⁻¹ᵁ (Target i).basicOpen r),
        ∀ s : Γ(Model,completedMap i ⁻¹ᵁ (Target i).basicOpen r),
          Algebra.norm (DualNumber Γ(Target i,(Target i).basicOpen r))
            (TrivSqZeroExt.inl s : DualNumber Γ(Model,completedMap i ⁻¹ᵁ (Target i).basicOpen r)) =
              TrivSqZeroExt.inl (CompletedCharacterOpenNorm318.norm i ((Target i).basicOpen r) s) ∧
          Units.map (Algebra.norm (DualNumber Γ(Target i,(Target i).basicOpen r)))
            (SquareZeroUnit318.unit Γ(Model,completedMap i ⁻¹ᵁ (Target i).basicOpen r) s) =
              SquareZeroUnit318.unit Γ(Target i,(Target i).basicOpen r)
                (CompletedCharacterOpenTrace318.trace i ((Target i).basicOpen r) s) := by
  obtain ⟨b,r,hx,⟨bs⟩⟩ := CharacterActualPrincipalBasis318.cover i x
  letI : Nonempty ((Target i).basicOpen r) := ⟨⟨x,hx⟩⟩
  refine ⟨b,r,hx,bs,fun s => ⟨?_,?_⟩⟩
  · exact OriginalFiniteFreeDualTransfer318.norm_coefficient (completedMap i) (hasBasis i)
      ((Target i).basicOpen r) ((chart_affine i b).basicOpen r) bs s
  · exact OriginalFiniteFreeDualTransfer318.norm_unit (completedMap i) (hasBasis i) (generic_finite i)
      ((Target i).basicOpen r) ((chart_affine i b).basicOpen r) bs s
end CharacterActualLocalDualNorm318
