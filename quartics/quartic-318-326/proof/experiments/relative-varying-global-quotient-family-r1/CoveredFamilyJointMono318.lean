module
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace CoveredFamilyJointMono318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Joint monicity of the ambient and base maps survives literal base
change. No monicity of the old-ambient map alone is assumed. -/
lemma restrict {X C B T : Scheme.{u}} (a : X ⟶ C) (p : X ⟶ B)
    (h : ∀ {W : Scheme.{u}} (v w : W ⟶ X),v ≫ a=w ≫ a → v ≫ p=w ≫ p → v=w)
    (q : T ⟶ B) {W : Scheme.{u}} (v w : W ⟶ pullback p q)
    (ha : v ≫ pullback.fst p q ≫ a=w ≫ pullback.fst p q ≫ a)
    (hp : v ≫ pullback.snd p q=w ≫ pullback.snd p q) : v=w := by
  apply pullback.hom_ext
  · apply h
    · simpa only [Category.assoc] using ha
    · simp only [Category.assoc,pullback.condition]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ q) hp
  · exact hp

/-- A full target open cover and actual Cartesian source charts suffice
to descend joint monicity. This is a scheme-arrow statement on arbitrary
test schemes, not injectivity on geometric points. -/
lemma of_cover {X C B : Scheme.{u}} (a : X ⟶ C) (p : X ⟶ B) (U : B.OpenCover)
    (Z : U.I₀ → Scheme.{u}) (z : ∀ i,Z i ⟶ X) (q : ∀ i,Z i ⟶ U.X i)
    (sq : ∀ i,IsPullback (z i) (q i) p (U.f i))
    (h : ∀ i {W : Scheme.{u}} (v w : W ⟶ Z i),
      v ≫ z i ≫ a=w ≫ z i ≫ a → v ≫ q i=w ≫ q i → v=w)
    {W : Scheme.{u}} (v w : W ⟶ X)
    (ha : v ≫ a=w ≫ a) (hp : v ≫ p=w ≫ p) : v=w := by
  apply (U.pullback₁ (v ≫ p)).hom_ext
  intro i
  change pullback.fst (v ≫ p) (U.f i) ≫ v=
    pullback.fst (v ≫ p) (U.f i) ≫ w
  let r := pullback.fst (v ≫ p) (U.f i)
  let s := pullback.snd (v ≫ p) (U.f i)
  have hv : (r ≫ v) ≫ p=s ≫ U.f i := by
    simpa only [r,s,Category.assoc] using pullback.condition (f:=v ≫ p) (g:=U.f i)
  have hw : (r ≫ w) ≫ p=s ≫ U.f i := by
    rw [Category.assoc,← hp,← Category.assoc]
    exact hv
  let v' := (sq i).lift (r ≫ v) s hv
  let w' := (sq i).lift (r ≫ w) s hw
  have he : v'=w' := h i v' w' (by
    simp only [v',w',IsPullback.lift_fst_assoc,Category.assoc]
    exact congrArg (fun k => r ≫ k) ha) (by
    simp only [v',w',IsPullback.lift_snd])
  have he' := congrArg (fun k => k ≫ z i) he
  simpa only [v',w',IsPullback.lift_fst] using he'
end CoveredFamilyJointMono318
