module
public import OriginalTensorFrameChange318
public import OriginalLineIsomUnitTorsor318
public import OriginalLineFrameUnitTorsor318
public section
noncomputable section
namespace OriginalTensorScalarNormalization318
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}
lemma right_trans (I A B C : X.Modules) (e : A ≅ B) (f : B ≅ C) :
    TensorSheafFunctor318.congr (Iso.refl I) (e ≪≫ f)=
      TensorSheafFunctor318.congr (Iso.refl I) e ≪≫
        TensorSheafFunctor318.congr (Iso.refl I) f := by
  apply Iso.ext
  apply OriginalTensorFrameChange318.pure_ext I A
  intro U m n
  change _=(TensorSheafFunctor318.congr (Iso.refl I) f).hom.app U
    ((TensorSheafFunctor318.congr (Iso.refl I) e).hom.app U
      (IntrinsicTensorSheaf318.pure I A U m n))
  simp only [TensorSheafNormalization318.congr_pure]
  rfl
/-- Exact scalar normalization of the ACTUAL sheafified tensor functor,
proved on all pure sections on all opens and detected by its universal map. -/
lemma right_scalar (I A : X.Modules) (u : Γ(X,⊤)ˣ) :
    TensorSheafFunctor318.congr (Iso.refl I) (ModuleScalarComposition318.unitIso A u)=
      ModuleScalarComposition318.unitIso (IntrinsicTensorSheaf318.tensor I A) u := by
  apply Iso.ext
  apply OriginalTensorFrameChange318.pure_ext I A
  intro U m n
  rw [TensorSheafNormalization318.congr_pure]
  change IntrinsicTensorSheaf318.pure I A U m
      ((ModuleScalar318.map A (u:Γ(X,⊤))).app U n)=
    (ModuleScalar318.map (IntrinsicTensorSheaf318.tensor I A) (u:Γ(X,⊤))).app U
      (IntrinsicTensorSheaf318.pure I A U m n)
  rw [ModuleScalar318.map_apply,ModuleScalar318.map_apply]
  unfold IntrinsicTensorSheaf318.pure
  rw [TensorProduct.tmul_smul,map_smul]
lemma scalar_natural {M N : X.Modules} (e : M ≅ N) (u : Γ(X,⊤)ˣ) :
    ModuleScalarComposition318.unitIso M u ≪≫ e=
      e ≪≫ ModuleScalarComposition318.unitIso N u := by
  apply Iso.ext
  exact ModuleScalar318.natural (u:Γ(X,⊤)) e.hom
lemma structure_scalar (u : Γ(X,⊤)ˣ) :
    ModuleScalarComposition318.unitIso (SheafOfModules.unit X.ringCatSheaf) u=
      StructureLineAutomorphisms318.iso X u := by
  apply Iso.ext
  exact ModuleScalar318.unit_eq (u:Γ(X,⊤))
end OriginalTensorScalarNormalization318
