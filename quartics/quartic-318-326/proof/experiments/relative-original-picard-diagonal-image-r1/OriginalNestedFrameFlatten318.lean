module
public import IteratedCoefficientFrameModel318
public section
noncomputable section
namespace OriginalNestedFrameFlatten318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X Y Z : Scheme.{u}} (L : Line X) (f : Y ⟶ X) (g : Z ⟶ Y)
@[expose] def comparison :
    (LineSheafPullback318.line g (LineSheafPullback318.line f L)).object ≅
      (LineSheafPullback318.line (g ≫ f) L).object :=
  (PullbackPathComposition318.iso g f (g ≫ f) rfl).app L.object
/-- Two-sided normalization of actual iterated line pullback frames.
The line and native pseudofunctor associator are retained, not redefined. -/
@[expose] def equivalence : Frames (LineSheafPullback318.line g (LineSheafPullback318.line f L)) ≃
    Frames (LineSheafPullback318.line (g ≫ f) L) :=
  OriginalFrameIsoEquivalence318.target (comparison L f g)
lemma forward (e : Frames (LineSheafPullback318.line g (LineSheafPullback318.line f L))) :
    equivalence L f g e=e ≪≫ comparison L f g := rfl
variable {Z' : Scheme.{u}} (g' : Z' ⟶ Y) (h : Z' ⟶ Z) (hh : h ≫ g=g')
/-- Full-frame coefficient naturality of flattening, using the genuine
module pseudofunctor associativity identity on the SAME original line. -/
lemma natural (e : Frames (LineSheafPullback318.line g (LineSheafPullback318.line f L))) :
    equivalence L f g' (OriginalFramePathTransport318.transport (LineSheafPullback318.line f L)
      h g g' hh e)=
    OriginalFramePathTransport318.transport L h (g ≫ f) (g' ≫ f)
      (by rw [←Category.assoc,hh]) (equivalence L f g e) := by
  change (OriginalFramePullback318.frame h (LineSheafPullback318.line g (LineSheafPullback318.line f L)) e ≪≫
    (PullbackPathComposition318.iso h g g' hh).app ((Scheme.Modules.pullback f).obj L.object)) ≪≫
      comparison L f g' = _
  change _ = OriginalFramePullback318.frame h (LineSheafPullback318.line (g ≫ f) L)
    (e ≪≫ comparison L f g) ≪≫
    (PullbackPathComposition318.iso h (g ≫ f) (g' ≫ f) (by rw [←Category.assoc,hh])).app L.object
  rw [OriginalFramePullbackCoherence318.target]
  apply Iso.ext
  simp only [comparison,Iso.trans_hom,Functor.mapIso_hom,Category.assoc]
  exact congrArg (fun k =>
    (OriginalFramePullback318.frame h (LineSheafPullback318.line g (LineSheafPullback318.line f L)) e).hom ≫ k)
    (PullbackPathComposition318.assoc h g f g' (g ≫ f) (g' ≫ f) hh rfl rfl
      (by rw [←Category.assoc,hh]) L.object)
end OriginalNestedFrameFlatten318
