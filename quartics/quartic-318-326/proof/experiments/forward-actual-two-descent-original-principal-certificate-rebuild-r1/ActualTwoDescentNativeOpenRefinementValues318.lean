module
public import ActualTwoDescentPushedStructureRefinement318
public section
noncomputable section
namespace ActualTwoDescentNativeOpenRefinementValues318
open CategoryTheory AlgebraicGeometry Opposite
open ActualTwoDescentNativeTensorRestrictionProducts318
open ActualTwoDescentOpenRestrictionAdjointComposition318 ActualTwoDescentTildeStructureNormalization318
universe u
variable {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (j : Y ⟶ X) (m : Z ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion m] (h : k ≫ j=m)

def source (M : X.Modules) : M.restrict m ⟶ (M.restrict j).restrict k :=
  (Scheme.Modules.restrictFunctorCongr h).inv.app M ≫
    (Scheme.Modules.restrictFunctorComp k j).hom.app M

def value (M : X.Modules) (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    M.restrict m ⟶ SheafOfModules.unit Z.ringCatSheaf :=
  source k j m h M ≫ restrictValue k f

lemma source_apply (M : X.Modules) (U : Z.Opens) (s : Γ(M,m ''ᵁ U)) :
    (source k j m h M).app U s=
      M.presheaf.map (eqToHom (show j ''ᵁ (k ''ᵁ U)=m ''ᵁ U by rw [←h]; simp)).op s := by
  change M.presheaf.map (eqToHom (show j ''ᵁ (k ''ᵁ U)=(k ≫ j) ''ᵁ U by simp)).op
    (M.presheaf.map (eqToHom (show (k ≫ j) ''ᵁ U=m ''ᵁ U by rw [h])).op s)=_
  rw [←Functor.map_comp_apply] <;> rfl

lemma source_pure (M N : X.Modules) (U : Z.Opens) (s : Γ(M,m ''ᵁ U)) (t : Γ(N,m ''ᵁ U)) :
    (source k j m h (IntrinsicTensorSheaf318.tensor M N)).app U
      (IntrinsicTensorSheaf318.pure M N (m ''ᵁ U) s t)=
    IntrinsicTensorSheaf318.pure M N (j ''ᵁ (k ''ᵁ U))
      ((source k j m h M).app U s) ((source k j m h N).app U t) := by
  rw [source_apply,source_apply,source_apply,IntrinsicTensorSheaf318.pure_restrict]

lemma value_apply (M : X.Modules) (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (U : Z.Opens) (s : Γ(M,m ''ᵁ U)) :
    (value k j m h M f).app U s=(k.appIso U).hom
      (f.app (k ''ᵁ U) ((source k j m h M).app U s)) := rfl

lemma value_adjoint (M : X.Modules) (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.restrictAdjunction m).homEquiv _ _ (value k j m h M f)=
    (Scheme.Modules.restrictAdjunction j).homEquiv _ _ f ≫
      ClutchedModule318.restriction j k ≫
      (Scheme.Modules.pushforwardCongr h).hom.app (SheafOfModules.unit Z.ringCatSheaf) := by
  unfold value source restrictValue
  simp only [Category.assoc]
  rw [congr_adjoint,composition,restrictUnit_adjoint]
  simp only [ClutchedModule318.restriction,Category.assoc]

/-- Pull an ACTUAL all-open product identity through a genuine
refinement. No injectivity or generic-function-field test is used. -/
lemma value_square_product (M : X.Modules)
    (f : M.restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (q : (IntrinsicTensorSheaf318.tensor M M).restrict j ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (a : Γ(Y,⊤))
    (hq : ∀ U (s t : Γ(M,j ''ᵁ U)),
      (Y.presheaf.map (homOfLE (show U≤⊤ from le_top)).op a)*
        q.app U (IntrinsicTensorSheaf318.pure M M (j ''ᵁ U) s t)=f.app U s*f.app U t)
    (U : Z.Opens) (s t : Γ(M,m ''ᵁ U)) :
    (Z.presheaf.map (homOfLE (show U≤⊤ from le_top)).op (k.appTop a))*
      (value k j m h (IntrinsicTensorSheaf318.tensor M M) q).app U
        (IntrinsicTensorSheaf318.pure M M (m ''ᵁ U) s t)=
    (value k j m h M f).app U s*(value k j m h M f).app U t := by
  have hh := congrArg (fun z => (k.appIso U).hom z)
    (hq (k ''ᵁ U) ((source k j m h M).app U s) ((source k j m h M).app U t))
  rw [map_mul,map_mul,scalar_restrict] at hh
  rw [value_apply,source_pure,value_apply,value_apply]
  exact hh
end ActualTwoDescentNativeOpenRefinementValues318
