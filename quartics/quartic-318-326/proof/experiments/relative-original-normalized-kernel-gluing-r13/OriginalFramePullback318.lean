module
public import OriginalLineFrameUnitTorsor318
public import LineSheafPullback318
public import OriginalSectionPullbackComposition318
public import PullbackScalar318
public section
noncomputable section
namespace OriginalFramePullback318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSectionPullbackComposition318
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Line Y)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual pullback of a full frame, including the canonical
pullback-of-structure-sheaf comparison. -/
@[expose] def frame (e : OriginalLineFrameUnitTorsor318.Frames L) :
    OriginalLineFrameUnitTorsor318.Frames (LineSheafPullback318.line f L) :=
  (IdentityCotangent318.pullbackUnitIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e

lemma unit_value :
    (IdentityCotangent318.pullbackUnitIso f).inv.app ⊤ (show Γ(X,⊤) from 1)=
      pull f (SheafOfModules.unit Y.ringCatSheaf) (show Γ(Y,⊤) from 1) := by
  have h := congrArg (fun q => q.app ⊤ (show Γ(Y,⊤) from 1))
    (PullbackScalar318.adjoint_unit f)
  change (IdentityCotangent318.pullbackUnitIso f).hom.app ⊤
    (pull f (SheafOfModules.unit Y.ringCatSheaf) 1)=f.appTop 1 at h
  rw [map_one] at h
  have hi := congrArg (fun q => q.app ⊤
    (pull f (SheafOfModules.unit Y.ringCatSheaf) (show Γ(Y,⊤) from 1)))
    (IdentityCotangent318.pullbackUnitIso f).hom_inv_id
  change (IdentityCotangent318.pullbackUnitIso f).inv.app ⊤
    ((IdentityCotangent318.pullbackUnitIso f).hom.app ⊤
      (pull f (SheafOfModules.unit Y.ringCatSheaf) 1))=_ at hi
  rw [h] at hi
  exact hi

/-- The FULL pulled frame has exactly the native adjunction-unit section
value. No arbitrary equivalence of section sets is substituted. -/
lemma value (e : OriginalLineFrameUnitTorsor318.Frames L) :
    (frame f L e).hom.app ⊤ 1=pull f L.object (e.hom.app ⊤ 1) := by
  change ((Scheme.Modules.pullback f).map e.hom).app ⊤
    ((IdentityCotangent318.pullbackUnitIso f).inv.app ⊤ (show Γ(X,⊤) from 1))=_
  rw [unit_value]
  exact naturality f e.hom (show Γ(Y,⊤) from 1)
end OriginalFramePullback318
