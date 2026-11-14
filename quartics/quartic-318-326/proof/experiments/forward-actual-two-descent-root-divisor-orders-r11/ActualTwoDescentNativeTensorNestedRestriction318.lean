module
public import ActualTwoDescentNativeTensorMapComposition318
public section
noncomputable section
namespace ActualTwoDescentNativeTensorNestedRestriction318
open CategoryTheory AlgebraicGeometry Opposite
open ActualTwoDescentNativeTensorMorphismProducts318 ActualTwoDescentNativeTensorRestrictionProducts318
universe u
variable {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (j : Y ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]

/-- The native tensor restriction isomorphism respects the EXACT native
composition comparison,including its open-set equality transports. -/
lemma tensor_composition (M N : X.Modules) :
    (Scheme.Modules.restrictFunctorComp k j).hom.app (IntrinsicTensorSheaf318.tensor M N) ≫
      (Scheme.Modules.restrictFunctor k).map (TensorOpenRestriction318.iso j M N).hom ≫
      (TensorOpenRestriction318.iso k (M.restrict j) (N.restrict j)).hom=
    (TensorOpenRestriction318.iso (k ≫ j) M N).hom ≫
      map ((Scheme.Modules.restrictFunctorComp k j).hom.app M)
        ((Scheme.Modules.restrictFunctorComp k j).hom.app N) := by
  apply hom_ext_restricted
  intro U s t
  let e : j ''ᵁ (k ''ᵁ U)=(k ≫ j) ''ᵁ U := by simp
  change (TensorOpenRestriction318.iso k (M.restrict j) (N.restrict j)).hom.app U
    ((TensorOpenRestriction318.iso j M N).hom.app (k ''ᵁ U)
      ((IntrinsicTensorSheaf318.tensor M N).presheaf.map (eqToHom e).op
        (IntrinsicTensorSheaf318.pure M N ((k ≫ j) ''ᵁ U) s t)))=
    (map _ _).app U ((TensorOpenRestriction318.iso (k ≫ j) M N).hom.app U _)
  rw [IntrinsicTensorSheaf318.pure_restrict,TensorSheafNormalization318.restriction_pure,
    TensorSheafNormalization318.restriction_pure,TensorSheafNormalization318.restriction_pure,map_pure] <;> rfl
end ActualTwoDescentNativeTensorNestedRestriction318
