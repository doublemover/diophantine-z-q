module
public import RelativeAffineTestGluing318
public section
noncomputable section
namespace RelativeAffineTestEvaluation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeAffineTestRule318 RelativeAffineTestGluing318
universe u
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R)) (F : Rule R p q)
local notation "U" => RelativeAffineTestCover318.cover R p
local instance chartAlgebra (i : U.I₀) : Algebra R (U.X i) := RelativeAffineTestCover318.algebra R p i
variable (S : CommRingCat.{u}) [Algebra R S] (x : Test R p S)
/-- The glued map realizes the prescribed operation on EVERY affine
test, proved on the entire affine refinement of its pulled-back cover. -/
lemma evaluate : x.val ≫ realize R p q F=(F.app S x).val := by
  let C := U.openCover.pullback₁ x.val
  let V := C.affineRefinement
  apply Scheme.Cover.hom_ext V.openCover _ _
  intro k
  let T := V.X k
  let f : Spec T ⟶ Spec S := V.f k
  let g : Spec T ⟶ Spec (U.X k.1) := (C.X k.1).affineOpenCover.f k.2 ≫ pullback.snd x.val (U.f k.1)
  have hs : f ≫ x.val=g ≫ U.f k.1 := by
    change ((C.X k.1).affineOpenCover.f k.2 ≫ pullback.fst x.val (U.f k.1)) ≫ x.val=
      ((C.X k.1).affineOpenCover.f k.2 ≫ pullback.snd x.val (U.f k.1)) ≫ U.f k.1
    rw [Category.assoc,Category.assoc,pullback.condition]
  letI : Algebra R T := ((Spec.preimage f).hom.comp (algebraMap R S)).toAlgebra
  let φ : S →ₐ[R] T := { __ := (Spec.preimage f).hom, commutes' := fun _ => rfl }
  have hf : Spec.map (CommRingCat.ofHom φ.toRingHom)=f := Spec.map_preimage _
  have hfb : f ≫ VaryingSourceCoefficientPullback318.base R S=VaryingSourceCoefficientPullback318.base R T := by
    rw [← hf]
    exact VaryingSourceCoefficientPullback318.coefficient_base R S T φ
  have hgb : g ≫ VaryingSourceCoefficientPullback318.base R (U.X k.1)=VaryingSourceCoefficientPullback318.base R T := by
    rw [← RelativeAffineTestCover318.over R p k.1,← Category.assoc,← hs,Category.assoc,x.property]
    exact hfb
  let y : Test R p T := map R p S T φ x
  have hy : f ≫ x.val=y.val := by change f ≫ x.val=Spec.map _ ≫ x.val; rw [hf]
  have h₁ := on_arrow R p q F S T f hfb x y hy
  have h₂ := on_arrow R p q F _ T g hgb (RelativeAffineTestCover318.point R p k.1) y (hs.symm.trans hy)
  have hc : f ≫ (F.app S x).val=g ≫ localMap R p q F k.1 := h₁.symm.trans h₂
  change f ≫ (x.val ≫ realize R p q F)=f ≫ (F.app S x).val
  rw [← Category.assoc,hs,Category.assoc,into_realize]
  exact hc.symm
/-- Whole-scheme uniqueness follows from its original full affine cover,
not from equality on geometric points. -/
lemma unique (f : X ⟶ Y) (hf : ∀ (S : CommRingCat.{u}) [Algebra R S] (x : Test R p S),
    x.val ≫ f=(F.app S x).val) : f=realize R p q F := by
  apply Scheme.Cover.hom_ext U.openCover _ _
  intro i
  exact (hf _ (RelativeAffineTestCover318.point R p i)).trans (into_realize R p q F i).symm
end RelativeAffineTestEvaluation318
