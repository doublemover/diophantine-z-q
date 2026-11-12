module
public import OriginalFrameDescentData318
public section
noncomputable section
namespace AffineFrameRule318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X : Scheme.{u}} (L : Line X)
/-- Actual full-frame data on ALL affine test maps, with naturality on
whole scheme arrows and the literal pullback path comparison. -/
structure Rule where
  app : ∀ (S : CommRingCat.{u}) (x : Spec S ⟶ X),Frames (LineSheafPullback318.line x L)
  natural : ∀ (S T : CommRingCat.{u}) (a : Spec T ⟶ Spec S)
    (x : Spec S ⟶ X) (y : Spec T ⟶ X) (h : a ≫ x=y),
    OriginalFramePullback318.frame a (LineSheafPullback318.line x L) (app S x) ≪≫
      (PullbackPathComposition318.iso a x y h).app L.object=app T y
@[expose] def ofFrame (e : Frames L) : Rule L where
  app _ x := OriginalFramePullback318.frame x L e
  natural _ _ a x y h := OriginalFramePullbackCoherence318.path a x L y h e
end AffineFrameRule318
