module
public import OriginalTensorOpenNaturality318
public section
noncomputable section
namespace OriginalTensorChartFrameNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}}
lemma congr_trans {M N M' N' M'' N'' : X.Modules}
    (e : M ≅ M') (f : N ≅ N') (e' : M' ≅ M'') (f' : N' ≅ N'') :
    TensorSheafFunctor318.congr (e ≪≫ e') (f ≪≫ f')=
      TensorSheafFunctor318.congr e f ≪≫ TensorSheafFunctor318.congr e' f' := by
  apply Iso.ext
  apply OriginalTensorFrameChange318.pure_ext M N
  intro U m n
  change _=(TensorSheafFunctor318.congr e' f').hom.app U
    ((TensorSheafFunctor318.congr e f).hom.app U (IntrinsicTensorSheaf318.pure M N U m n))
  simp only [TensorSheafNormalization318.congr_pure]
  rfl
/-- The entire tensor chart frame, including the original native open
comparison, is natural in both complete original line isomorphisms. -/
lemma frame {M N M' N' : X.Modules} (a : M ≅ M') (b : N ≅ N') (U : X.Opens)
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
    (f : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ N.restrict U.ι) :
    TensorLineLocalFrame318.frame M N U e f ≪≫
      (Scheme.Modules.restrictFunctor U.ι).mapIso (TensorSheafFunctor318.congr a b)=
    TensorLineLocalFrame318.frame M' N' U
      (e ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso a)
      (f ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso b) := by
  have h := congrArg Iso.hom (OriginalTensorOpenNaturality318.natural U.ι a b)
  have hi := congrArg (fun q => (TensorOpenRestriction318.iso U.ι M N).inv ≫ q ≫
      (TensorOpenRestriction318.iso U.ι M' N').inv) h
  simp only [Iso.trans_hom,Category.assoc,Iso.hom_inv_id,Category.comp_id,
    Iso.inv_hom_id_assoc] at hi
  apply Iso.ext
  simp only [TensorLineLocalFrame318.frame,congr_trans,Iso.trans_hom,
    Iso.symm_hom,Category.assoc]
  rw [hi]
end OriginalTensorChartFrameNaturality318
