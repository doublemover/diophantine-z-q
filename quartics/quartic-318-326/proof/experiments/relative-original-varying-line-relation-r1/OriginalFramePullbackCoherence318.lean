module
public import OriginalFramePullback318
public import ModuleTopExt318
public section
noncomputable section
namespace OriginalFramePullbackCoherence318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line Z)
/-- Entire frames compose through the actual module pullback associator. -/
lemma composition (e : Frames L) :
    OriginalFramePullback318.frame f (LineSheafPullback318.line g L)
      (OriginalFramePullback318.frame g L e) ≪≫
        (Scheme.Modules.pullbackComp f g).app L.object=
    OriginalFramePullback318.frame (f ≫ g) L e := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  change ((Scheme.Modules.pullbackComp f g).hom.app L.object).app ⊤
    ((OriginalFramePullback318.frame f (LineSheafPullback318.line g L)
      (OriginalFramePullback318.frame g L e)).hom.app ⊤ 1)=_
  rw [OriginalFramePullback318.value,OriginalFramePullback318.value,
    OriginalFramePullback318.value]
  exact OriginalSectionPullbackComposition318.composition f g L.object (e.hom.app ⊤ 1)

lemma path (k : X ⟶ Z) (h : f ≫ g=k) (e : Frames L) :
    OriginalFramePullback318.frame f (LineSheafPullback318.line g L)
      (OriginalFramePullback318.frame g L e) ≪≫
        (PullbackPathComposition318.iso f g k h).app L.object=
    OriginalFramePullback318.frame k L e := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  change ((PullbackPathComposition318.iso f g k h).hom.app L.object).app ⊤
    ((OriginalFramePullback318.frame f (LineSheafPullback318.line g L)
      (OriginalFramePullback318.frame g L e)).hom.app ⊤ 1)=_
  rw [OriginalFramePullback318.value,OriginalFramePullback318.value,
    OriginalFramePullback318.value]
  exact OriginalSectionPullbackComposition318.path f g k h L.object (e.hom.app ⊤ 1)

variable {Y' : Scheme.{u}} (f' : X ⟶ Y') (g' : Y' ⟶ Z)
  (h : f ≫ g=f' ≫ g')
@[expose] def squareIso :
    (LineSheafPullback318.line f (LineSheafPullback318.line g L)).object ≅
      (LineSheafPullback318.line f' (LineSheafPullback318.line g' L)).object :=
  (Scheme.Modules.pullbackComp f g).app L.object ≪≫
    (Scheme.Modules.pullbackCongr h).app L.object ≪≫
      ((Scheme.Modules.pullbackComp f' g').app L.object).symm
/-- The literal geometric square, including its full sheaf comparison,
commutes on entire frame isomorphisms over arbitrary schemes. -/
lemma square (e : Frames L) :
    OriginalFramePullback318.frame f (LineSheafPullback318.line g L)
      (OriginalFramePullback318.frame g L e) ≪≫ squareIso f g L f' g' h=
    OriginalFramePullback318.frame f' (LineSheafPullback318.line g' L)
      (OriginalFramePullback318.frame g' L e) := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  change (squareIso f g L f' g' h).hom.app ⊤
    ((OriginalFramePullback318.frame f (LineSheafPullback318.line g L)
      (OriginalFramePullback318.frame g L e)).hom.app ⊤ 1)=_
  rw [OriginalFramePullback318.value,OriginalFramePullback318.value,
    OriginalFramePullback318.value,OriginalFramePullback318.value]
  exact OriginalSectionPullbackComposition318.square f g f' g' h L.object (e.hom.app ⊤ 1)

variable {M N : Line Y}
/-- Change of target retains the literal frame and the whole module iso. -/
lemma target (a : M.object ≅ N.object) (e : Frames M) :
    OriginalFramePullback318.frame f N (e ≪≫ a)=
      OriginalFramePullback318.frame f M e ≪≫ (Scheme.Modules.pullback f).mapIso a := by
  apply Iso.ext
  simp only [OriginalFramePullback318.frame,Iso.trans_hom,Functor.mapIso_hom,
    Functor.map_comp,Category.assoc]
end OriginalFramePullbackCoherence318
