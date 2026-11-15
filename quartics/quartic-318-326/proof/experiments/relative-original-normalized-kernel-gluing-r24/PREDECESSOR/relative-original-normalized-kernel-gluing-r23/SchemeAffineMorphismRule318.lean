module
public import RelativeAffineTestEvaluation318
public section
noncomputable section
namespace SchemeAffineMorphismRule318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (X Y : Scheme.{u})
/-- Natural operations on all affine tests of the original whole scheme. -/
structure Rule where
  app : ∀ (R : CommRingCat.{u}), (Spec R ⟶ X) → (Spec R ⟶ Y)
  natural : ∀ (R S : CommRingCat.{u}) (g : Spec S ⟶ Spec R)
    (x : Spec R ⟶ X) (y : Spec S ⟶ X), g ≫ x=y → app S y=g ≫ app R x
variable {X Y} (F : Rule X Y)
local notation "U" => X.affineOpenCover
@[expose] def localMap (i : U.I₀) : Spec (U.X i) ⟶ Y := F.app _ (U.f i)
lemma compatible (i j : U.I₀) : pullback.fst (U.f i) (U.f j) ≫ localMap F i=
    pullback.snd (U.f i) (U.f j) ≫ localMap F j := by
  let V := (pullback (U.f i) (U.f j)).affineOpenCover
  apply Scheme.Cover.hom_ext V.openCover _ _
  intro k
  let l := V.f k ≫ pullback.fst (U.f i) (U.f j)
  let r := V.f k ≫ pullback.snd (U.f i) (U.f j)
  have hr : r ≫ U.f j=l ≫ U.f i := by simp only [r,l,Category.assoc,pullback.condition]
  have h₁ := F.natural _ _ l (U.f i) (l ≫ U.f i) rfl
  have h₂ := F.natural _ _ r (U.f j) (l ≫ U.f i) hr
  simpa only [localMap,l,r,Category.assoc] using h₁.symm.trans h₂
/-- The actual whole-scheme morphism, glued on entire affine overlaps. -/
@[expose] def realize : X ⟶ Y := U.openCover.glueMorphisms (localMap F) (compatible F)
@[reassoc] lemma into_realize (i : U.I₀) : U.f i ≫ realize F=localMap F i :=
  U.openCover.ι_glueMorphisms _ _ i
end SchemeAffineMorphismRule318
