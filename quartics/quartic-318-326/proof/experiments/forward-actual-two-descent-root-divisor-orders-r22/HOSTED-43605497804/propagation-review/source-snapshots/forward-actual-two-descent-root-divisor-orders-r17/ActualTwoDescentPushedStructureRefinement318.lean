module
public import ActualTwoDescentOriginalInfinitySquareRestriction318
public section
noncomputable section
namespace ActualTwoDescentPushedStructureRefinement318
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X Y Z T : Scheme.{u}}

/-- Actual pushed structure restrictions compose through a refinement.
The ambient equality transport is retained,including its direction. -/
lemma restriction_refinement (j : Y ⟶ X) (l : Z ⟶ Y) (k : T ⟶ Z)
    (m : T ⟶ Y) (h : k ≫ l=m) :
    ClutchedModule318.restriction j l ≫ ClutchedModule318.restriction (l ≫ j) k ≫
      (Scheme.Modules.pushforwardCongr (show k ≫ (l ≫ j)=m ≫ j by
        rw [←Category.assoc,h])).hom.app (SheafOfModules.unit T.ringCatSheaf)=
    ClutchedModule318.restriction j m := by
  subst m
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change T.presheaf.map (𝟙 (op (k⁻¹ᵁ (l⁻¹ᵁ (j⁻¹ᵁ U)))))
    (k.app (l⁻¹ᵁ (j⁻¹ᵁ U)) (l.app (j⁻¹ᵁ U) s))=_
  rw [Functor.map_id,ConcreteCategory.id_apply] <;> rfl
end ActualTwoDescentPushedStructureRefinement318
