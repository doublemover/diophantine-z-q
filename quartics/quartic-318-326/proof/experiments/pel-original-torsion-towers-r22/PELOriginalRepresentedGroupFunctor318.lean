module
public import PELOriginalSchemePointGroup318
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public section
noncomputable section
namespace PELOriginalRepresentedGroupFunctor318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalProductChartCover318 PELOriginalSchemePointGroup318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The actual original candidate as an object over Spec(C). -/
@[expose] def candidateOver : Over (Spec (CommRingCat.of ℂ)) := Over.mk (π τ hτ)

/-- A genuine commutative-group-valued functor on ALL complex schemes,
represented on underlying sets by the SAME original candidate. -/
@[expose] def groupFunctor : (Over (Spec (CommRingCat.of ℂ)))ᵒᵖ ⥤ AddCommGrpCat where
  obj Y := AddCommGrpCat.of (Points τ hτ Y.unop.left Y.unop.hom)
  map f := AddCommGrpCat.ofHom (pull τ hτ _ f.unop.left f.unop.w)
  map_id Y := by
    apply AddCommGrpCat.ext
    intro p
    apply Subtype.ext
    exact Category.id_comp p.val
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro p
    apply Subtype.ext
    exact Category.assoc g.unop.left f.unop.left p.val

/-- Literal represented-point equivalence, with both inverse maps.
It preserves full morphisms over C, rather than only closed points. -/
@[expose] def pointEquiv (Y : Over (Spec (CommRingCat.of ℂ))) :
    Points τ hτ Y.left Y.hom ≃ (Y ⟶ candidateOver τ hτ) where
  toFun p := Over.homMk p.val p.property
  invFun p := ⟨p.left,p.w⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Over.OverMorphism.ext; rfl

/-- Exact Yoneda naturality of the representing equivalence. Together
with groupFunctor this gives a represented commutative group functor
whose addition, inverse and identity are the constructed regular maps. -/
lemma pointEquiv_natural {Y Z : Over (Spec (CommRingCat.of ℂ))}
    (f : Z ⟶ Y) (p : Points τ hτ Y.left Y.hom) :
    pointEquiv τ hτ Z ((pull τ hτ Y.hom f.left f.w) p)=f≫pointEquiv τ hτ Y p := by
  apply Over.OverMorphism.ext
  rfl
end PELOriginalRepresentedGroupFunctor318
