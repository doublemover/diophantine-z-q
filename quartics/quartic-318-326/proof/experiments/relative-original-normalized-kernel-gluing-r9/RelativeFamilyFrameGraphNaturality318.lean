module
public import RelativeFamilyFrameGraph318
public section
noncomputable section
namespace RelativeFamilyFrameGraphNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open RelativeFamilyFrameGraph318 OriginalFramePathTransport318
universe u
variable {X B : Scheme.{u}} (p : X ⟶ B) (L : Line X)
  (F : RelativeFamilyFrameRule318.Rule p L)
lemma natural (S T : CommRingCat.{u}) (g : Spec T ⟶ Spec S)
    (x : Spec S ⟶ X) (y : Spec T ⟶ X) (h : g ≫ x=y) :
    transport L g x y h (frame p L F S x)=frame p L F T y := by
  let hb : g ≫ (x ≫ p)=y ≫ p := by rw [←Category.assoc,h]
  let a := RelativeSchemeCoefficient318.map p (x ≫ p) (y ≫ p) g hb
  have ha : a ≫ pullback.fst p (x ≫ p)=pullback.fst p (y ≫ p) :=
    RelativeSchemeCoefficient318.map_fst p _ _ _ _
  have hn : transport L a (pullback.fst p (x ≫ p)) (pullback.fst p (y ≫ p)) ha
      (F.app S (x ≫ p))=F.app T (y ≫ p) := F.natural S T g _ _ hb
  change transport L g x y h
    (transport L (graph p S x) (pullback.fst p (x ≫ p)) x (graph_fst p S x) (F.app S (x ≫ p)))=
    transport L (graph p T y) (pullback.fst p (y ≫ p)) y (graph_fst p T y) (F.app T (y ≫ p))
  rw [←hn,composition,composition]
  apply arrow_congr
  exact square p S T g x y h
/-- Base-affine family data yields actual natural frames on ALL affine
source tests by pulling along genuine graph maps, including non-flat graphs. -/
@[expose] def rule : AffineFrameRule318.Rule L where
  app := frame p L F
  natural := natural p L F
end RelativeFamilyFrameGraphNaturality318
