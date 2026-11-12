module
public import AffineFrameRuleEquivalence318
public section
noncomputable section
namespace AffineFrameRulePullback318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Line Y) (F : AffineFrameRule318.Rule L)
/-- Pullback of all-affine-test frame data is constructed from its genuine
global descent, not by adding a global-frame assumption to the input. -/
@[expose] def map : AffineFrameRule318.Rule (LineSheafPullback318.line f L) :=
  AffineFrameRule318.ofFrame (LineSheafPullback318.line f L)
    (OriginalFramePullback318.frame f L ((AffineFrameRuleEquivalence318.equivalence L).symm F))
/-- The resulting operation is exactly affine-test precomposition,
including the native full pullback associator. -/
lemma app (S : CommRingCat.{u}) (x : Spec S ⟶ X) :
    (map f L F).app S x ≪≫ (Scheme.Modules.pullbackComp x f).app L.object=
      F.app S (x ≫ f) := by
  change OriginalFramePullback318.frame x (LineSheafPullback318.line f L)
    (OriginalFramePullback318.frame f L ((AffineFrameRuleEquivalence318.equivalence L).symm F)) ≪≫ _=_
  rw [OriginalFramePullbackCoherence318.composition]
  exact AffineFrameRuleRecovery318.evaluate L F Y.affineOpenCover S (x ≫ f)
lemma recover : (AffineFrameRuleEquivalence318.equivalence (LineSheafPullback318.line f L)).symm
    (map f L F)=OriginalFramePullback318.frame f L
      ((AffineFrameRuleEquivalence318.equivalence L).symm F) :=
  (AffineFrameRuleEquivalence318.equivalence (LineSheafPullback318.line f L)).symm_apply_apply _
end AffineFrameRulePullback318
