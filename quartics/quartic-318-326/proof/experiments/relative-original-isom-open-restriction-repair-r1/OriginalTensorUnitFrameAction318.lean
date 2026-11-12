module
public import OriginalLineTensorPullbackNormalization318
public section
noncomputable section
namespace OriginalTensorUnitFrameAction318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}}
local notation "O" => SheafOfModules.unit X.ringCatSheaf
/-- Exact native unit-tensor comparison multiplies the two ACTUAL
regular units. The proof tests pure sections on every open. -/
lemma unit_square (a b : Γ(X,⊤)ˣ) :
    TensorSheafFunctor318.congr (StructureLineAutomorphisms318.iso X a)
      (StructureLineAutomorphisms318.iso X b) ≪≫ TensorSheafFunctor318.unitIso=
    TensorSheafFunctor318.unitIso ≪≫ StructureLineAutomorphisms318.iso X (a*b) := by
  rw [←OriginalTensorScalarNormalization318.structure_scalar,
    ←OriginalTensorScalarNormalization318.structure_scalar,
    ←OriginalTensorScalarNormalization318.structure_scalar]
  apply Iso.ext
  apply OriginalTensorFrameChange318.pure_ext O O
  intro U m n
  change TensorSheafFunctor318.unitIso.hom.app U
      ((TensorSheafFunctor318.congr (ModuleScalarComposition318.unitIso O a)
        (ModuleScalarComposition318.unitIso O b)).hom.app U
          (IntrinsicTensorSheaf318.pure O O U m n))=
    (ModuleScalar318.map O ((a*b:Γ(X,⊤)ˣ):Γ(X,⊤))).app U
      (TensorSheafFunctor318.unitIso.hom.app U (IntrinsicTensorSheaf318.pure O O U m n))
  rw [TensorSheafNormalization318.congr_pure,TensorSheafNormalization318.unitIso_pure,
    TensorSheafNormalization318.unitIso_pure]
  change ((ModuleScalar318.map O (a:Γ(X,⊤))).app U m)*
      ((ModuleScalar318.map O (b:Γ(X,⊤))).app U n)=_
  rw [ModuleScalar318.map_apply,ModuleScalar318.map_apply,ModuleScalar318.map_apply]
  change ((X.presheaf.map (homOfLE le_top).op (a:Γ(X,⊤)))*m)*
      ((X.presheaf.map (homOfLE le_top).op (b:Γ(X,⊤)))*n)=
    (X.presheaf.map (homOfLE le_top).op ((a*b:Γ(X,⊤)ˣ):Γ(X,⊤)))*(m*n)
  rw [Units.val_mul,map_mul]
  ring
lemma inverse_square (a b : Γ(X,⊤)ˣ) :
    TensorSheafFunctor318.unitIso.inv ≫
      (TensorSheafFunctor318.congr (StructureLineAutomorphisms318.iso X a)
        (StructureLineAutomorphisms318.iso X b)).hom=
    (StructureLineAutomorphisms318.iso X (a*b)).hom ≫ TensorSheafFunctor318.unitIso.inv := by
  apply (cancel_mono TensorSheafFunctor318.unitIso.hom).mp
  have h := congrArg Iso.hom (unit_square a b)
  simpa only [Iso.trans_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id,
    Iso.inv_hom_id_assoc] using congrArg (fun q => TensorSheafFunctor318.unitIso.inv ≫ q) h
/-- Changing BOTH complete original local frames multiplies the tensor
frame by the exact product unit on that same open subscheme. -/
lemma frame (M N : X.Modules) (U : X.Opens)
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
    (f : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ N.restrict U.ι)
    (a b : Γ(U.toScheme,⊤)ˣ) :
    TensorLineLocalFrame318.frame M N U
      (StructureLineAutomorphisms318.iso U.toScheme a ≪≫ e)
      (StructureLineAutomorphisms318.iso U.toScheme b ≪≫ f)=
    StructureLineAutomorphisms318.iso U.toScheme (a*b) ≪≫
      TensorLineLocalFrame318.frame M N U e f := by
  apply Iso.ext
  simp only [TensorLineLocalFrame318.frame,OriginalTensorChartFrameNaturality318.congr_trans,
    Iso.trans_hom,Iso.symm_hom]
  simp only [Category.assoc]
  rw [←Category.assoc TensorSheafFunctor318.unitIso.inv,
    inverse_square]
  simp only [Category.assoc]
end OriginalTensorUnitFrameAction318
