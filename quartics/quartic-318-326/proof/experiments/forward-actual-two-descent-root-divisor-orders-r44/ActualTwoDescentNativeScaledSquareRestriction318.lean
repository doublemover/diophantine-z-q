module
public import ActualTwoDescentNativeTensorNestedRestriction318
public section
noncomputable section
namespace ActualTwoDescentNativeScaledSquareRestriction318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentNativeTensorMorphismProducts318 ActualTwoDescentNativeTensorMapComposition318
open ActualTwoDescentNativeTensorRestrictionProducts318 ActualTwoDescentNativeTensorNestedRestriction318
open ActualTwoDescentScaledNativeTensorSquareFrame318
universe u
variable {X Y Z : Scheme.{u}}

def squareMap (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf) (a : Γ(Y,⊤)) :
    (IntrinsicTensorSheaf318.tensor M M).restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  (TensorOpenRestriction318.iso j M M).hom ≫ product f f ≫ ClutchedModule318.multiply a

lemma squareMap_scaled (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) (a : Γ(Y,⊤)) (ha : IsUnit a) :
    (scaledSquareFrame j M e a ha).hom=squareMap j M e.hom a := by
  apply hom_ext_restricted
  intro U s t
  change _=(ClutchedModule318.multiply a).app U
    ((product e.hom e.hom).app U ((TensorOpenRestriction318.iso j M M).hom.app U _))
  rw [scaledSquareFrame_pure,TensorSheafNormalization318.restriction_pure,
    product_pure,ClutchedModule318.multiply_apply]

def composedValue (k : Z ⟶ Y) (j : Y ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j]
    (M : X.Modules) (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    M.restrict (k ≫ j) ⟶ SheafOfModules.unit Z.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorComp k j).hom.app M ≫ restrictValue k f

lemma restrictValue_comp (k : Z ⟶ Y) [IsOpenImmersion k] {M N : Y.Modules}
    (f : M ⟶ N) (g : N ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    restrictValue k (f ≫ g)=(Scheme.Modules.restrictFunctor k).map f ≫ restrictValue k g := by
  simp only [restrictValue,Functor.map_comp,Category.assoc]

/-- Exact nested restriction of a scaled square. The coefficient is the
actual appTop image and the frame is the old native composite,not selected anew. -/
lemma squareMap_restrict (k : Z ⟶ Y) (j : Y ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] (M : X.Modules)
    (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf) (a : Γ(Y,⊤)) :
    (Scheme.Modules.restrictFunctorComp k j).hom.app (IntrinsicTensorSheaf318.tensor M M) ≫
      restrictValue k (squareMap j M f a)=
    squareMap (k ≫ j) M (composedValue k j M f) (k.appTop a) := by
  unfold squareMap
  rw [restrictValue_comp]
  change _ ≫ (Scheme.Modules.restrictFunctor k).map (TensorOpenRestriction318.iso j M M).hom ≫
    ((Scheme.Modules.restrictFunctor k).map (product f f ≫ ClutchedModule318.multiply a) ≫
      (Scheme.Modules.restrictUnitIso k).hom)=_
  rw [scaled_product_restrict]
  calc
    _ = ((Scheme.Modules.restrictFunctorComp k j).hom.app (IntrinsicTensorSheaf318.tensor M M) ≫
      (Scheme.Modules.restrictFunctor k).map (TensorOpenRestriction318.iso j M M).hom ≫
      (TensorOpenRestriction318.iso k (M.restrict j) (M.restrict j)).hom) ≫
        product (restrictValue k f) (restrictValue k f) ≫ ClutchedModule318.multiply (k.appTop a) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [tensor_composition]
      simp only [Category.assoc]
      rw [←Category.assoc (map _ _) (product _ _) (ClutchedModule318.multiply (k.appTop a)),map_product] <;> rfl
end ActualTwoDescentNativeScaledSquareRestriction318
