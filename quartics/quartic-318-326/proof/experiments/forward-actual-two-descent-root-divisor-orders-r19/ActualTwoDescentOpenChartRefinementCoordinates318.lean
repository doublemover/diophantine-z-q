module
public import ActualTwoDescentOpenChartCoordinateNaturality318
public section
noncomputable section
namespace ActualTwoDescentOpenChartRefinementCoordinates318
open CategoryTheory AlgebraicGeometry Opposite
open ActualTwoDescentOpenChartAmbientCoordinates318 ActualTwoDescentNativeOpenRefinementValues318
universe u
variable {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (j : Y ⟶ X) (m : Z ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion m] (h : k ≫ j=m)
    (M : X.Modules) (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf)

/-- Exact refinement invariance for ambient coordinates. The actual
adjoint and structure map are consumed,not an image-frame normalization
postulated separately. Every ambient subopen of the refinement is covered. -/
lemma coordinate_refinement (V : X.Opens) (hV : V≤m.opensRange) (hVj : V≤j.opensRange)
    (s : Γ(M,V)) :
    coordinate m M (value k j m h M f) V hV s=coordinate j M f V hVj s := by
  subst m
  apply (ConcreteCategory.bijective_of_isIso (ambientRingIso (k ≫ j) V hV).hom).injective
  rw [ambientRingIso_hom,coordinate_structure]
  change ((Scheme.Modules.restrictAdjunction (k ≫ j)).homEquiv _ _
    (value k j (k ≫ j) rfl M f)).app V s=(k ≫ j).app V (coordinate j M f V hVj s)
  rw [value_adjoint]
  change Z.presheaf.map (𝟙 (op (k⁻¹ᵁ (j⁻¹ᵁ V))))
    (k.app (j⁻¹ᵁ V) ((adjoint j M f).app V s))=
      k.app (j⁻¹ᵁ V) (j.app V (coordinate j M f V hVj s))
  rw [Functor.map_id,ConcreteCategory.id_apply,coordinate_structure]
end ActualTwoDescentOpenChartRefinementCoordinates318
