module
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace SchemeMonoLocalLift318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y Z : Scheme.{u}} (U : X.OpenCover) (j : Y ⟶ Z) [Mono j] (f : X ⟶ Z)
  (g : ∀ i, U.X i ⟶ Y) (h : ∀ i, g i ≫ j=U.f i ≫ f)
include h in
lemma compatible (i k : U.I₀) : pullback.fst (U.f i) (U.f k) ≫ g i=
    pullback.snd (U.f i) (U.f k) ≫ g k := by
  apply (cancel_mono j).mp
  rw [Category.assoc,Category.assoc,h i,h k,← Category.assoc,← Category.assoc,pullback.condition]
@[expose] def lift : X ⟶ Y := U.glueMorphisms g (compatible U j f g h)
@[reassoc] lemma into_lift (i : U.I₀) : U.f i ≫ lift U j f g h=g i :=
  U.ι_glueMorphisms g (compatible U j f g h) i
@[reassoc] lemma lift_factor : lift U j f g h ≫ j=f := by
  apply Scheme.Cover.hom_ext U _ _
  intro i
  rw [← Category.assoc,into_lift,h i]
lemma unique (k : X ⟶ Y) (hk : k ≫ j=f) : k=lift U j f g h :=
  (cancel_mono j).mp (hk.trans (lift_factor U j f g h).symm)
end SchemeMonoLocalLift318
