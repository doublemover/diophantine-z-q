module
public import SchemeAffineMorphismRule318
public section
noncomputable section
namespace SchemeAffineMorphismEvaluation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeAffineMorphismRule318
universe u
variable {X Y : Scheme.{u}} (F : Rule X Y)
lemma evaluate (R : CommRingCat.{u}) (x : Spec R ⟶ X) : x ≫ realize F=F.app R x := by
  let U := X.affineOpenCover
  let C := U.openCover.pullback₁ x
  let V := C.affineRefinement
  apply Scheme.Cover.hom_ext V.openCover _ _
  intro k
  let f : Spec (V.X k) ⟶ Spec R := V.f k
  let g : Spec (V.X k) ⟶ Spec (U.X k.1) :=
    (C.X k.1).affineOpenCover.f k.2 ≫ pullback.snd x (U.f k.1)
  have hs : f ≫ x=g ≫ U.f k.1 := by
    change ((C.X k.1).affineOpenCover.f k.2 ≫ pullback.fst x (U.f k.1)) ≫ x=
      ((C.X k.1).affineOpenCover.f k.2 ≫ pullback.snd x (U.f k.1)) ≫ U.f k.1
    rw [Category.assoc,Category.assoc,pullback.condition]
  have h₁ := F.natural R (V.X k) f x (f ≫ x) rfl
  have h₂ := F.natural (U.X k.1) (V.X k) g (U.f k.1) (f ≫ x) hs.symm
  change f ≫ (x ≫ realize F)=f ≫ F.app R x
  rw [←Category.assoc,hs,Category.assoc,into_realize]
  exact h₂.symm.trans h₁
lemma hom_ext (f g : X ⟶ Y)
    (h : ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ X), x ≫ f=x ≫ g) : f=g := by
  apply Scheme.Cover.hom_ext X.affineOpenCover.openCover _ _
  intro i
  exact h _ (X.affineOpenCover.f i)
lemma unique (f : X ⟶ Y)
    (h : ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ X), x ≫ f=F.app R x) : f=realize F := by
  apply hom_ext
  intro R x
  exact (h R x).trans (evaluate F R x).symm
end SchemeAffineMorphismEvaluation318
