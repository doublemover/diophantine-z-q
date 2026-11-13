module
public import ActualTwoDescentOriginalRootFullOverlap318
public section
noncomputable section
namespace ActualTwoDescentNativeTensorMapComposition318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentNativeTensorMorphismProducts318
universe u
variable {X : Scheme.{u}}

lemma map_comp {M N P Q R S : X.Modules} (f : M ⟶ P) (g : N ⟶ Q)
    (h : P ⟶ R) (k : Q ⟶ S) :
    map f g ≫ map h k=map (f ≫ h) (g ≫ k) := by
  apply hom_ext_pure
  intro U s t
  change (map h k).app U ((map f g).app U _)=_
  rw [map_pure,map_pure,map_pure] <;> rfl

lemma map_product {M N P Q : X.Modules} (f : M ⟶ P) (g : N ⟶ Q)
    (h : P ⟶ SheafOfModules.unit X.ringCatSheaf)
    (k : Q ⟶ SheafOfModules.unit X.ringCatSheaf) :
    map f g ≫ product h k=product (f ≫ h) (g ≫ k) := by
  unfold product
  rw [←Category.assoc,map_comp]

/-- Whole-map tensor naturality under the ACTUAL open restriction. -/
lemma map_restrict {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M N P Q : X.Modules} (f : M ⟶ P) (g : N ⟶ Q) :
    (Scheme.Modules.restrictFunctor j).map (map f g) ≫ (TensorOpenRestriction318.iso j P Q).hom=
    (TensorOpenRestriction318.iso j M N).hom ≫
      map ((Scheme.Modules.restrictFunctor j).map f) ((Scheme.Modules.restrictFunctor j).map g) := by
  apply ActualTwoDescentNativeTensorRestrictionProducts318.hom_ext_restricted
  intro U s t
  change (TensorOpenRestriction318.iso j P Q).hom.app U ((map f g).app (j ''ᵁ U) _)=
    (map _ _).app U ((TensorOpenRestriction318.iso j M N).hom.app U _)
  rw [map_pure,TensorSheafNormalization318.restriction_pure,
    TensorSheafNormalization318.restriction_pure,map_pure] <;> rfl
end ActualTwoDescentNativeTensorMapComposition318
