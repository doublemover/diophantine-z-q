module
public import RelativeAffineTestCover318
public section
noncomputable section
namespace RelativeAffineTestGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeAffineTestRule318
universe u
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R)) (F : Rule R p q)
local notation "U" => RelativeAffineTestCover318.cover R p
local instance chartAlgebra (i : U.I₀) : Algebra R (U.X i) := RelativeAffineTestCover318.algebra R p i
@[expose] def localMap (i : U.I₀) : Spec (U.X i) ⟶ Y :=
  (F.app _ (RelativeAffineTestCover318.point R p i)).val
lemma compatible (i j : U.I₀) : pullback.fst (U.f i) (U.f j) ≫ localMap R p q F i=
    pullback.snd (U.f i) (U.f j) ≫ localMap R p q F j := by
  let V := (pullback (U.f i) (U.f j)).affineOpenCover
  apply Scheme.Cover.hom_ext V.openCover _ _
  intro k
  let T := V.X k
  let l : Spec T ⟶ Spec (U.X i) := V.f k ≫ pullback.fst (U.f i) (U.f j)
  let r : Spec T ⟶ Spec (U.X j) := V.f k ≫ pullback.snd (U.f i) (U.f j)
  let g : Spec T ⟶ X := l ≫ U.f i
  have hr : r ≫ U.f j=g := by simp only [r,g,l,Category.assoc,pullback.condition]
  letI : Algebra R T := (Spec.preimage (g ≫ p)).hom.toAlgebra
  have hg : g ≫ p=VaryingSourceCoefficientPullback318.base R T := (Spec.map_preimage _).symm
  let z : Test R p T := ⟨g,hg⟩
  have hlb : l ≫ VaryingSourceCoefficientPullback318.base R (U.X i)=VaryingSourceCoefficientPullback318.base R T := by
    rw [← RelativeAffineTestCover318.over R p i,← Category.assoc]
    exact hg
  have hrb : r ≫ VaryingSourceCoefficientPullback318.base R (U.X j)=VaryingSourceCoefficientPullback318.base R T := by
    rw [← RelativeAffineTestCover318.over R p j,← Category.assoc,hr]
    exact hg
  have h₁ := on_arrow R p q F _ T l hlb (RelativeAffineTestCover318.point R p i) z rfl
  have h₂ := on_arrow R p q F _ T r hrb (RelativeAffineTestCover318.point R p j) z hr
  simpa only [localMap,l,r,Category.assoc] using h₁.symm.trans h₂
/-- Realization as a GENUINE scheme morphism, obtained by gluing on the
whole original scheme's affine cover and checking its entire overlaps. -/
@[expose] def realize : X ⟶ Y := U.openCover.glueMorphisms (localMap R p q F) (compatible R p q F)
@[reassoc] lemma into_realize (i : U.I₀) : U.f i ≫ realize R p q F=localMap R p q F i :=
  U.openCover.ι_glueMorphisms _ _ i
@[reassoc] lemma over : realize R p q F ≫ q=p := by
  apply Scheme.Cover.hom_ext U.openCover _ _
  intro i
  rw [← Category.assoc,into_realize]
  exact (F.app _ (RelativeAffineTestCover318.point R p i)).property.trans
    (RelativeAffineTestCover318.over R p i).symm
end RelativeAffineTestGluing318
