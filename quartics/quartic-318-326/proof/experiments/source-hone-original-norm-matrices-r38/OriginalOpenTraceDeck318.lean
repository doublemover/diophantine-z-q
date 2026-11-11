module
public import OpenDominantTrace318
public import OpenFunctionField318

public section
noncomputable section
namespace OriginalOpenTraceDeck318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f] (e : X ≅ X)

theorem preimage (h : e.hom ≫ f = f) (U : Y.Opens) :
    e.hom ⁻¹ᵁ (f ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
  change (e.hom ≫ f) ⁻¹ᵁ U = f ⁻¹ᵁ U
  rw [h]

/-- The original generic-stalk map of a deck isomorphism fixes the actual quotient field. -/
@[expose] def fieldEquiv (h : e.hom ≫ f = f) :
    letI := AffineDominantNorm318.fieldAlgebra f
    X.functionField ≃ₐ[Y.functionField] X.functionField := by
  letI := AffineDominantNorm318.fieldAlgebra f
  refine { OpenFunctionField318.fieldEquiv e.hom with commutes' := ?_ }
  intro y
  have hm : DominantFunctionField318.map (e.hom ≫ f)=DominantFunctionField318.map f := by
    have heq : (⟨e.hom ≫ f,inferInstance⟩ : {g : X ⟶ Y // IsDominant g}) =
        ⟨f,inferInstance⟩ := Subtype.ext h
    exact congrArg (fun g : {g : X ⟶ Y // IsDominant g} =>
      @DominantFunctionField318.map X Y _ _ g.val g.property) heq
  have hc := hm.symm.trans (DominantFunctionField318.map_comp e.hom f)
  have he := congrArg (fun m : Y.functionField ⟶ X.functionField => m y) hc.symm
  exact he

/-- Literal section pullback on a stable open has the original generic-stalk action. -/
theorem section_germ (h : e.hom ≫ f = f) (U : Y.Opens) [Nonempty U]
    (s : Γ(X,f ⁻¹ᵁ U)) :
    letI : Nonempty (f ⁻¹ᵁ U) := DominantFunctionField318.preimage_nonempty f U
    X.germToFunctionField (f ⁻¹ᵁ U)
      (e.hom.appLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) (le_of_eq (preimage f e h U).symm) s) =
      OpenFunctionField318.fieldEquiv e.hom (X.germToFunctionField (f ⁻¹ᵁ U) s) := by
  letI : Nonempty (f ⁻¹ᵁ U) := DominantFunctionField318.preimage_nonempty f U
  letI : Nonempty (e.hom ⁻¹ᵁ (f ⁻¹ᵁ U)) :=
    DominantFunctionField318.preimage_nonempty e.hom (f ⁻¹ᵁ U)
  have hm := congrArg (fun m : Γ(X,f ⁻¹ᵁ U) ⟶ X.functionField => m s)
    (OpenFunctionField318.fieldIso_germ e.hom (f ⁻¹ᵁ U))
  change X.germToFunctionField (f ⁻¹ᵁ U)
    (X.presheaf.map (homOfLE (le_of_eq (preimage f e h U).symm)).op
      (e.hom.app (f ⁻¹ᵁ U) s)) = _
  rw [AffineDominantNormRestriction318.germ_restrict]
  exact hm.symm

/-- The original all-open regular-function trace is invariant under every actual deck isomorphism. -/
theorem trace_invariant [IsFinite f] (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
    (h : e.hom ≫ f = f) (U : Y.Opens) (s : Γ(X,f ⁻¹ᵁ U)) :
    OpenDominantTrace318.trace f hY hfinite U
      (e.hom.appLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) (le_of_eq (preimage f e h U).symm) s) =
      OpenDominantTrace318.trace f hY hfinite U s := by
  classical
  by_cases hu : Nonempty U
  · letI := hu
    letI : Nonempty (f ⁻¹ᵁ U) := DominantFunctionField318.preimage_nonempty f U
    letI := AffineDominantNorm318.fieldAlgebra f
    apply Y.germToFunctionField_injective U
    rw [OpenDominantTrace318.trace_embedding,OpenDominantTrace318.trace_embedding,section_germ]
    exact Algebra.trace_eq_of_algEquiv (fieldEquiv f e h) _
  · letI := OpenDominantTrace318.empty_subsingleton U hu
    exact Subsingleton.elim _ _

end OriginalOpenTraceDeck318
