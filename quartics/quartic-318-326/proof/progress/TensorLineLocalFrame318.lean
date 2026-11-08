module
public import TensorSheafNormalization318
public import OpenLineFrameCoordinates318
public section
noncomputable section
namespace TensorLineLocalFrame318
open AlgebraicGeometry CategoryTheory Opposite
open IntrinsicTensorSheaf318
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M N:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (f:SheafOfModules.unit U.toScheme.ringCatSheaf≅N.restrict U.ι)
/-- A genuine unit frame of the actual tensor sheaf on the original open. -/
@[expose] def frame:SheafOfModules.unit U.toScheme.ringCatSheaf≅(tensor M N).restrict U.ι:=
  TensorSheafFunctor318.unitIso.symm ≪≫TensorSheafFunctor318.congr e f ≪≫
    (TensorOpenRestriction318.iso U.ι M N).symm
lemma hom_inv:(frame M N U e f).hom≫(frame M N U e f).inv=𝟙 _:=
  (frame M N U e f).hom_inv_id
lemma inv_hom:(frame M N U e f).inv≫(frame M N U e f).hom=𝟙 _:=
  (frame M N U e f).inv_hom_id
/-- Exact coefficient multiplication on actual pure sections, with no
unproved tensor/presheaf identification or scalar normalization. -/
lemma inverse_pure (W:U.toScheme.Opens)
    (m:Γ(M,U.ι.opensFunctor.obj W)) (n:Γ(N,U.ι.opensFunctor.obj W)):
    (frame M N U e f).inv.val.app (op W) (pure M N (U.ι.opensFunctor.obj W) m n)=
      (fun a b:Γ(U.toScheme,W)=>a*b) (e.inv.val.app (op W) m) (f.inv.val.app (op W) n):=by
  change TensorSheafFunctor318.unitIso.hom.val.app (op W)
    ((TensorSheafFunctor318.congr e f).inv.val.app (op W)
      ((TensorOpenRestriction318.iso U.ι M N).hom.val.app (op W)
        (pure M N (U.ι.opensFunctor.obj W) m n)))=_
  have h1:=TensorSheafNormalization318.restriction_pure U.ι M N W m n
  have h2:=TensorSheafNormalization318.congr_pure e.symm f.symm W m n
  have h3:=TensorSheafNormalization318.unitIso_pure W
    (show Γ(U.toScheme,W) from e.inv.val.app (op W) m)
    (show Γ(U.toScheme,W) from f.inv.val.app (op W) n)
  exact (congrArg (fun z=>TensorSheafFunctor318.unitIso.hom.val.app (op W)
    ((TensorSheafFunctor318.congr e f).inv.val.app (op W) z)) h1).trans
      ((congrArg (fun z=>TensorSheafFunctor318.unitIso.hom.val.app (op W) z) h2).trans h3)
end TensorLineLocalFrame318
