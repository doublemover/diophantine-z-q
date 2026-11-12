module
public import ActualTwoDescentOriginalMatchedSquareIsomorphisms318
public section
noncomputable section
namespace ActualTwoDescentNativeTensorRestrictionProducts318
open CategoryTheory AlgebraicGeometry Opposite
open ActualTwoDescentNativeTensorMorphismProducts318
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

lemma restriction_inv_pure (M N : Y.Modules) (U : X.Opens)
    (s : Γ(M,j ''ᵁ U)) (t : Γ(N,j ''ᵁ U)) :
    (TensorOpenRestriction318.iso j M N).inv.app U
      (IntrinsicTensorSheaf318.pure (M.restrict j) (N.restrict j) U s t)=
        IntrinsicTensorSheaf318.pure M N (j ''ᵁ U) s t := by
  have h := congrArg ((TensorOpenRestriction318.iso j M N).inv.app U)
    (TensorSheafNormalization318.restriction_pure j M N U s t)
  have hi := congrArg (fun f => f.app U (IntrinsicTensorSheaf318.pure M N (j ''ᵁ U) s t))
    (TensorOpenRestriction318.iso j M N).hom_inv_id
  exact h.symm.trans hi

/-- Test maps from the RESTRICTION of the native global tensor on all
ambient pure tensors,using its actual restriction isomorphism. -/
lemma hom_ext_restricted {M N : Y.Modules} {P : X.Modules}
    (f g : (IntrinsicTensorSheaf318.tensor M N).restrict j ⟶ P)
    (h : ∀ U (s : Γ(M,j ''ᵁ U)) (t : Γ(N,j ''ᵁ U)),
      f.app U (IntrinsicTensorSheaf318.pure M N (j ''ᵁ U) s t)=
      g.app U (IntrinsicTensorSheaf318.pure M N (j ''ᵁ U) s t)) : f=g := by
  apply (cancel_epi (TensorOpenRestriction318.iso j M N).inv).mp
  apply hom_ext_pure
  intro U s t
  change f.app U ((TensorOpenRestriction318.iso j M N).inv.app U _)=
    g.app U ((TensorOpenRestriction318.iso j M N).inv.app U _)
  rw [restriction_inv_pure]
  exact h U s t

def restrictValue {M : Y.Modules} (f : M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    M.restrict j ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor j).map f ≫ (Scheme.Modules.restrictUnitIso j).hom

lemma product_restrict {M N : Y.Modules}
    (f : M ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (g : N ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor j).map (product f g) ≫ (Scheme.Modules.restrictUnitIso j).hom=
    (TensorOpenRestriction318.iso j M N).hom ≫ product (restrictValue j f) (restrictValue j g) := by
  apply hom_ext_restricted
  intro U s t
  change (j.appIso U).hom ((product f g).app (j ''ᵁ U) _)=
    (product (restrictValue j f) (restrictValue j g)).app U
      ((TensorOpenRestriction318.iso j M N).hom.app U _)
  rw [product_pure,TensorSheafNormalization318.restriction_pure,product_pure,map_mul]
  rfl

/-- Pullback of a global regular scalar is the SAME native appTop
map on every subopen,not an independent scalar choice. -/
lemma scalar_restrict (U : X.Opens) (a : Γ(Y,⊤)) :
    (j.appIso U).hom (Y.presheaf.map (homOfLE (show j ''ᵁ U≤⊤ from le_top)).op a)=
      X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op (j.appTop a) := by
  have h : Y.presheaf.map (homOfLE (show j ''ᵁ U≤⊤ from le_top)).op ≫
      (j.appIso U).hom=j.appTop ≫ X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op := by
    rw [Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE]
    rfl
  exact congrArg (fun f => f a) h

lemma multiply_restrict (a : Γ(Y,⊤)) :
    (Scheme.Modules.restrictFunctor j).map (ClutchedModule318.multiply a) ≫
      (Scheme.Modules.restrictUnitIso j).hom=
    (Scheme.Modules.restrictUnitIso j).hom ≫ ClutchedModule318.multiply (j.appTop a) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (j.appIso U).hom ((ClutchedModule318.multiply a).app (j ''ᵁ U) s)=
    (ClutchedModule318.multiply (j.appTop a)).app U ((j.appIso U).hom s)
  rw [ClutchedModule318.multiply_apply,ClutchedModule318.multiply_apply,map_mul,scalar_restrict]

lemma scaled_product_restrict {M N : Y.Modules}
    (f : M ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (g : N ⟶ SheafOfModules.unit Y.ringCatSheaf) (a : Γ(Y,⊤)) :
    (Scheme.Modules.restrictFunctor j).map (product f g ≫ ClutchedModule318.multiply a) ≫
      (Scheme.Modules.restrictUnitIso j).hom=
    (TensorOpenRestriction318.iso j M N).hom ≫ product (restrictValue j f) (restrictValue j g) ≫
      ClutchedModule318.multiply (j.appTop a) := by
  rw [Functor.map_comp,Category.assoc,multiply_restrict,←Category.assoc,product_restrict]
  simp only [Category.assoc]
end ActualTwoDescentNativeTensorRestrictionProducts318
