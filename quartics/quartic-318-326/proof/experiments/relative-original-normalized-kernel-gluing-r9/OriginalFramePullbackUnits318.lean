module
public import OriginalFramePullback318
public section
noncomputable section
namespace OriginalFramePullbackUnits318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalLineFrameUnitTorsor318
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Line Y)
@[expose] def units : Γ(Y,⊤)ˣ →* Γ(X,⊤)ˣ := Units.map f.appTop.hom.toMonoidHom

lemma unit_inverse_square (u : Γ(Y,⊤)ˣ) :
    (IdentityCotangent318.pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (ClutchedModule318.multiply (u:Γ(Y,⊤)))=
    ClutchedModule318.multiply (units f u : Γ(X,⊤)) ≫
      (IdentityCotangent318.pullbackUnitIso f).inv := by
  apply (cancel_mono (IdentityCotangent318.pullbackUnitIso f).hom).mp
  have h := congrArg (fun q => (IdentityCotangent318.pullbackUnitIso f).inv ≫ q)
    (PullbackScalar318.pullback_multiply f (u:Γ(Y,⊤)))
  simpa only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id] using h

/-- Exact unit equivariance of actual full frame pullback on EVERY
scheme morphism, with native regular-function pullback and unit comparison. -/
lemma action (u : Γ(Y,⊤)ˣ) (e : Frames L) :
    OriginalFramePullback318.frame f L (act L u e)=
      act (LineSheafPullback318.line f L) (units f u) (OriginalFramePullback318.frame f L e) := by
  apply Iso.ext
  change (IdentityCotangent318.pullbackUnitIso f).inv ≫
    (Scheme.Modules.pullback f).map ((StructureLineAutomorphisms318.iso Y u).hom ≫ e.hom)=_
  rw [Functor.map_comp,←Category.assoc]
  change ((IdentityCotangent318.pullbackUnitIso f).inv ≫
    (Scheme.Modules.pullback f).map (ClutchedModule318.multiply (u:Γ(Y,⊤)))) ≫
      (Scheme.Modules.pullback f).map e.hom=_
  rw [unit_inverse_square,Category.assoc]
  rfl

lemma ratio_natural (e d : Frames L) :
    ratio (LineSheafPullback318.line f L)
      (OriginalFramePullback318.frame f L e) (OriginalFramePullback318.frame f L d)=
        units f (ratio L e d) := by
  have h := congrArg (OriginalFramePullback318.frame f L) (ratio_act L e d)
  rw [action] at h
  rw [←h,act_ratio]
end OriginalFramePullbackUnits318
