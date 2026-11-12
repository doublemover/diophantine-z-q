module
public import AffineFrameRuleEquivalence318
public section
noncomputable section
namespace OriginalFramePathTransport318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X Y Z W : Scheme.{u}} (L : Line X)
@[expose] def transport (f : Z ⟶ Y) (y : Y ⟶ X) (z : Z ⟶ X) (h : f ≫ y=z)
    (e : Frames (LineSheafPullback318.line y L)) : Frames (LineSheafPullback318.line z L) :=
  OriginalFramePullback318.frame f (LineSheafPullback318.line y L) e ≪≫
    (PullbackPathComposition318.iso f y z h).app L.object
lemma arrow_congr (f g : Z ⟶ Y) (y : Y ⟶ X) (z : Z ⟶ X)
    (hf : f ≫ y=z) (hg : g ≫ y=z) (h : f=g)
    (e : Frames (LineSheafPullback318.line y L)) : transport L f y z hf e=transport L g y z hg e := by
  subst g
  rfl
/-- Path transport is strictly compatible with actual composition after
retaining the native module pseudofunctor associator. -/
lemma composition (f : Z ⟶ Y) (g : W ⟶ Z) (y : Y ⟶ X) (z : Z ⟶ X) (w : W ⟶ X)
    (hf : f ≫ y=z) (hg : g ≫ z=w) (e : Frames (LineSheafPullback318.line y L)) :
    transport L g z w hg (transport L f y z hf e)=
      transport L (g ≫ f) y w (by rw [Category.assoc,hf]; exact hg) e := by
  unfold transport
  rw [OriginalFramePullbackCoherence318.target]
  apply Iso.ext
  let a := (PullbackPathComposition318.iso f y z hf).app L.object
  let b := (PullbackPathComposition318.iso g z w hg).app L.object
  let d := (PullbackPathComposition318.iso g f (g ≫ f) rfl).app
    ((Scheme.Modules.pullback y).obj L.object)
  let q := (PullbackPathComposition318.iso (g ≫ f) y w
    (by rw [Category.assoc,hf]; exact hg)).app L.object
  let v := (OriginalFramePullback318.frame g
    (LineSheafPullback318.line f (LineSheafPullback318.line y L))
    (OriginalFramePullback318.frame f (LineSheafPullback318.line y L) e)).hom
  have hs : d.hom ≫ q.hom=(Scheme.Modules.pullback g).map a.hom ≫ b.hom :=
    PullbackPathComposition318.assoc g f y (g ≫ f) z w rfl hf
      (by rw [Category.assoc,hf]; exact hg) hg L.object
  have hp : v ≫ d.hom=(OriginalFramePullback318.frame (g ≫ f)
      (LineSheafPullback318.line y L) e).hom :=
    congrArg Iso.hom (OriginalFramePullbackCoherence318.path g f
      (LineSheafPullback318.line y L) (g ≫ f) rfl e)
  change (v ≫ (Scheme.Modules.pullback g).map a.hom) ≫ b.hom=
    (OriginalFramePullback318.frame (g ≫ f) (LineSheafPullback318.line y L) e).hom ≫ q.hom
  rw [Category.assoc,←hs,←Category.assoc,hp]
end OriginalFramePathTransport318
