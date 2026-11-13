module
public import ActualTwoDescentOriginalInfinityFractionalSheafRebuild318
public import OpenFunctionField318
public section
noncomputable section
namespace ActualTwoDescentOpenRationalEvaluationRebuild318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (j : Y ⟶ X) [IsOpenImmersion j]

/-- Every nonempty ambient open meets the actual integral open chart. -/
lemma preimage_nonempty (U : X.Opens) [Nonempty U] : Nonempty (j ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint Y,?_⟩⟩
  change j (genericPoint Y) ∈ U
  rw [genericPoint_eq_of_isOpenImmersion j]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

local instance (U : X.Opens) [Nonempty U] : Nonempty (j ⁻¹ᵁ U) := preimage_nonempty j U

/-- Actual section germ followed by the inverse ACTUAL open-chart stalk map. -/
def evaluation (U : X.Opens) [Nonempty U] : Γ(Y,j ⁻¹ᵁ U) →+* X.functionField :=
  (OpenFunctionField318.fieldEquiv j).symm.toRingHom.comp
    (Y.germToFunctionField (j ⁻¹ᵁ U)).hom

lemma injective (U : X.Opens) [Nonempty U] : Function.Injective (evaluation j U) :=
  (OpenFunctionField318.fieldEquiv j).symm.injective.comp
    (Y.germToFunctionField_injective (j ⁻¹ᵁ U))

lemma ambient (U : X.Opens) [Nonempty U] (a : Γ(X,U)) :
    evaluation j U (j.app U a)=X.germToFunctionField U a := by
  apply (OpenFunctionField318.fieldEquiv j).injective
  have h := congrArg (fun k => k a) (OpenFunctionField318.fieldIso_germ j U)
  change OpenFunctionField318.fieldEquiv j (X.germToFunctionField U a)=
    Y.germToFunctionField (j ⁻¹ᵁ U) (j.app U a) at h
  change OpenFunctionField318.fieldEquiv j
    ((OpenFunctionField318.fieldEquiv j).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  exact h.symm

lemma restrict (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)
    (a : Γ(Y,j ⁻¹ᵁ U)) :
    evaluation j V (Y.presheaf.map (homOfLE (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from
      fun x hx => h hx)).op a)=evaluation j U a := by
  apply congrArg (OpenFunctionField318.fieldEquiv j).symm
  exact Y.presheaf.germ_res_apply (homOfLE (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from
    fun x hx => h hx)) (genericPoint Y) _ a
end ActualTwoDescentOpenRationalEvaluationRebuild318
