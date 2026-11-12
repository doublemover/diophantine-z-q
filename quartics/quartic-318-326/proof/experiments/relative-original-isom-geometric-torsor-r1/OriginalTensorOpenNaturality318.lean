module
public import OriginalChartPullbackFrameNaturality318
public section
noncomputable section
namespace OriginalTensorOpenNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
lemma inverse_pure (M N : Y.Modules) (U : X.Opens)
    (m : Γ(M,j.opensFunctor.obj U)) (n : Γ(N,j.opensFunctor.obj U)) :
    (TensorOpenRestriction318.iso j M N).inv.app U
      (IntrinsicTensorSheaf318.pure (M.restrict j) (N.restrict j) U m n)=
      IntrinsicTensorSheaf318.pure M N (j.opensFunctor.obj U) m n := by
  have h := congrArg (fun a => a.app U (IntrinsicTensorSheaf318.pure M N (j.opensFunctor.obj U) m n))
    (TensorOpenRestriction318.iso j M N).hom_inv_id
  change (TensorOpenRestriction318.iso j M N).inv.app U
    ((TensorOpenRestriction318.iso j M N).hom.app U
      (IntrinsicTensorSheaf318.pure M N (j.opensFunctor.obj U) m n))=_ at h
  rw [TensorSheafNormalization318.restriction_pure] at h
  exact h
/-- Native tensor/open-restriction comparison commutes with arbitrary
whole module isomorphisms. Every pure section on every source open is used. -/
lemma natural {M N M' N' : Y.Modules} (e : M ≅ M') (f : N ≅ N') :
    (Scheme.Modules.restrictFunctor j).mapIso (TensorSheafFunctor318.congr e f) ≪≫
        TensorOpenRestriction318.iso j M' N'=
      TensorOpenRestriction318.iso j M N ≪≫
        TensorSheafFunctor318.congr ((Scheme.Modules.restrictFunctor j).mapIso e)
          ((Scheme.Modules.restrictFunctor j).mapIso f) := by
  apply Iso.ext
  apply (cancel_epi (TensorOpenRestriction318.iso j M N).inv).mp
  apply OriginalTensorFrameChange318.pure_ext (M.restrict j) (N.restrict j)
  intro U m n
  change (TensorOpenRestriction318.iso j M' N').hom.app U
      ((TensorSheafFunctor318.congr e f).hom.app (j.opensFunctor.obj U)
        ((TensorOpenRestriction318.iso j M N).inv.app U
          (IntrinsicTensorSheaf318.pure (M.restrict j) (N.restrict j) U m n)))=
    (TensorSheafFunctor318.congr ((Scheme.Modules.restrictFunctor j).mapIso e)
      ((Scheme.Modules.restrictFunctor j).mapIso f)).hom.app U
      ((TensorOpenRestriction318.iso j M N).hom.app U
        ((TensorOpenRestriction318.iso j M N).inv.app U
          (IntrinsicTensorSheaf318.pure (M.restrict j) (N.restrict j) U m n)))
  rw [inverse_pure,TensorSheafNormalization318.congr_pure,
    TensorSheafNormalization318.restriction_pure,inverse_pure,
    TensorSheafNormalization318.restriction_pure,TensorSheafNormalization318.congr_pure]
  rfl
end OriginalTensorOpenNaturality318
