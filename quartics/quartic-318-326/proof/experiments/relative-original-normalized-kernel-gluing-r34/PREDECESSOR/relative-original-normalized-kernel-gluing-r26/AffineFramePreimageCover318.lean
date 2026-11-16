module
public import AffineFrameRuleGluing318
public section
noncomputable section
namespace AffineFramePreimageCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} (U : X.AffineOpenCover) (S : CommRingCat.{u}) (x : Spec S ⟶ X)
abbrev pulled := U.openCover.pullback₁ x
abbrev cover : (Spec S).AffineOpenCover := (pulled U S x).affineRefinement
abbrev intoChart (i : (cover U S x).I₀) : Spec ((cover U S x).X i) ⟶ Spec (U.X i.1) :=
  ((pulled U S x).X i.1).affineOpenCover.f i.2 ≫ pullback.snd x (U.f i.1)
@[reassoc] lemma square (i : (cover U S x).I₀) :
    intoChart U S x i ≫ U.f i.1=(cover U S x).f i ≫ x := by
  change (((pulled U S x).X i.1).affineOpenCover.f i.2 ≫ pullback.snd x (U.f i.1)) ≫ U.f i.1=
    (((pulled U S x).X i.1).affineOpenCover.f i.2 ≫ pullback.fst x (U.f i.1)) ≫ x
  rw [Category.assoc,Category.assoc,pullback.condition]
/-- Full preimage-cover refinement for EVERY affine test, including
non-open, non-flat and nonreduced test maps. -/
lemma image_cover : ⊤≤⨆i,(cover U S x).f i ''ᵁ ⊤ :=
  AffineFrameRuleGluing318.image_cover (cover U S x)
end AffineFramePreimageCover318
