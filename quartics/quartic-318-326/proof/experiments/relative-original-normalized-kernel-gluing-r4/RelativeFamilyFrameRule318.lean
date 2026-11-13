module
public import OriginalFramePathTransport318
public import RelativeSchemeCoefficient318
public section
noncomputable section
namespace RelativeFamilyFrameRule318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X B : Scheme.{u}} (p : X ⟶ B) (L : Line X)
/-- Full frames on every actual affine BASE test, with whole-family
coefficient naturality. Neither a global frame nor base affineness is assumed. -/
structure Rule where
  app : ∀ (S : CommRingCat.{u}) (b : Spec S ⟶ B),
    Frames (LineSheafPullback318.line (pullback.fst p b) L)
  natural : ∀ (S T : CommRingCat.{u}) (g : Spec T ⟶ Spec S)
    (b : Spec S ⟶ B) (a : Spec T ⟶ B) (h : g ≫ b=a),
    OriginalFramePathTransport318.transport L (RelativeSchemeCoefficient318.map p b a g h)
      (pullback.fst p b) (pullback.fst p a) (RelativeSchemeCoefficient318.map_fst p b a g h)
      (app S b)=app T a
@[expose] def ofFrame (e : Frames L) : Rule p L where
  app _ b := OriginalFramePullback318.frame (pullback.fst p b) L e
  natural _ _ g b a h := OriginalFramePullbackCoherence318.path
    (RelativeSchemeCoefficient318.map p b a g h) (pullback.fst p b) L
    (pullback.fst p a) (RelativeSchemeCoefficient318.map_fst p b a g h) e
end RelativeFamilyFrameRule318
