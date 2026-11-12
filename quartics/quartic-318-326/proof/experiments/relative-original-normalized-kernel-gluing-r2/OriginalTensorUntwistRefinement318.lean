module
public import OriginalTensorUntwistOver318
public import OpenLineFrameRefinement318
public import OriginalTensorFrameChange318
public section
noncomputable section
namespace OriginalTensorUntwistRefinement318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (L N : Line X) (U : X.Opens)
  (e : N.object.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
  (W : X.Opens) (h : W ≤ U)

/-- Actual restriction of the full-chart untwisting isomorphism on the
original over-open site, including BOTH original endpoint comparisons. -/
def restrictedIso : (LineSheafTensor318.line L N).object.over W ≅ L.object.over W :=
  ((SheafOfModules.overFunctorMap (R:=X.ringCatSheaf) (homOfLE h)).app
    (LineSheafTensor318.line L N).object).symm ≪≫
  (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso
    (OriginalTensorUntwistOver318.iso L N U e) ≪≫
  (SheafOfModules.overFunctorMap (R:=X.ringCatSheaf) (homOfLE h)).app L.object

lemma restriction_inv_pure (Z : W.toScheme.Opens)
    (m : Γ(L.object,W.ι ''ᵁ Z)) (n : Γ(N.object,W.ι ''ᵁ Z)) :
    (TensorOpenRestriction318.iso W.ι L.object N.object).inv.app Z
      (IntrinsicTensorSheaf318.pure (L.object.restrict W.ι) (N.object.restrict W.ι) Z m n) =
      IntrinsicTensorSheaf318.pure L.object N.object (W.ι ''ᵁ Z) m n := by
  have hp := TensorSheafNormalization318.restriction_pure W.ι L.object N.object Z m n
  have hi := congrArg (fun s => (TensorOpenRestriction318.iso W.ι L.object N.object).inv.app Z s) hp
  have he : (TensorOpenRestriction318.iso W.ι L.object N.object).inv.app Z
      ((TensorOpenRestriction318.iso W.ι L.object N.object).hom.app Z
        (IntrinsicTensorSheaf318.pure L.object N.object (W.ι ''ᵁ Z) m n)) =
      IntrinsicTensorSheaf318.pure L.object N.object (W.ι ''ᵁ Z) m n :=
    congrArg (fun q => q.app Z (IntrinsicTensorSheaf318.pure L.object N.object (W.ι ''ᵁ Z) m n))
      (TensorOpenRestriction318.iso W.ι L.object N.object).hom_inv_id
  exact hi.symm.trans he

/-- Restricting the ACTUAL chart untwisting map equals untwisting by the
ACTUAL restricted old frame. The proof detects original tensor morphisms
on all pure sections on all opens, rather than assuming a coordinate square. -/
lemma refinement : restrictedIso L N U e W h =
    OriginalTensorUntwistOver318.iso L N W
      (OpenLineFrameRefinement318.frame N.object U e.symm W h).symm := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv W).functor.map_injective
  apply (cancel_mono (((Scheme.Modules.overFunctorEquiv W).app L.object).hom)).mp
  apply (cancel_epi ((TensorOpenRestriction318.iso W.ι L.object N.object).inv ≫
    ((Scheme.Modules.overFunctorEquiv W).app (LineSheafTensor318.line L N).object).inv)).mp
  apply OriginalTensorFrameChange318.pure_ext (L.object.restrict W.ι) (N.object.restrict W.ι)
  intro Z m n
  change OriginalTensorUntwistOver318.sections L N U e (W.ι ''ᵁ Z)
      ((show W.ι ''ᵁ Z ≤ W from by simpa using W.ι.image_le_opensRange Z).trans h)
      ((TensorOpenRestriction318.iso W.ι L.object N.object).inv.app Z
        (IntrinsicTensorSheaf318.pure (L.object.restrict W.ι) (N.object.restrict W.ι) Z m n)) =
    OriginalTensorUntwistOver318.sections L N W
      (OpenLineFrameRefinement318.frame N.object U e.symm W h).symm (W.ι ''ᵁ Z)
      (by simpa using W.ι.image_le_opensRange Z)
      ((TensorOpenRestriction318.iso W.ι L.object N.object).inv.app Z
        (IntrinsicTensorSheaf318.pure (L.object.restrict W.ι) (N.object.restrict W.ι) Z m n))
  rw [restriction_inv_pure,OriginalTensorUntwistOver318.pure,OriginalTensorUntwistOver318.pure]
  simp only [Iso.symm_symm_eq,OpenLineFrameRefinement318.coordinates]

/-- Every original ambient subopen, and every section, satisfies the exact
nested coordinate equality. No local generation of global sections is used. -/
lemma sections (V : X.Opens) (hV : V ≤ W)
    (s : Γ((LineSheafTensor318.line L N).object,V)) :
    OriginalTensorUntwistOver318.sections L N U e V (hV.trans h) s =
      OriginalTensorUntwistOver318.sections L N W
        (OpenLineFrameRefinement318.frame N.object U e.symm W h).symm V hV s := by
  have hi := congrArg (fun q => q.hom.val.app (op (Over.mk (homOfLE hV))) s)
    (refinement L N U e W h)
  exact hi
end OriginalTensorUntwistRefinement318
