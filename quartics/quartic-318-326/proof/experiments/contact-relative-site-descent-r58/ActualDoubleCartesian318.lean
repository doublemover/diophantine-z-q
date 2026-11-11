module
public import AffineMorphismGlobalRecovery318
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public section
noncomputable section
namespace ActualDoubleCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B B' U U' : Scheme.{u}} (f : U ⟶ B) (g : U' ⟶ B')
  (a : U' ⟶ U) (b : B' ⟶ B) (h : a ≫ f = g ≫ b)
  (H : IsPullback a g f b)

include H in
/-- A Cartesian covering-arrow square induces a Cartesian square on the
original categorical double, over the original base arrow. This proves
coverage of actual doubles instead of assuming it from tensor coordinates. -/
lemma isPullback : IsPullback (doubleMap f g a b h) (first g ≫ g) (first f ≫ f) b := by
  apply IsPullback.mk'
  · rw [← Category.assoc,double_first,Category.assoc,h,← Category.assoc]
  · intro T x y hx hy
    apply pullback.hom_ext
    · apply H.hom_ext
      · simpa only [Category.assoc,← double_first] using congrArg (fun z => z ≫ first f) hx
      · simpa only [Category.assoc] using hy
    · apply H.hom_ext
      · simpa only [Category.assoc,← double_second] using congrArg (fun z => z ≫ second f) hx
      · simpa only [Category.assoc,← edge_condition g] using hy
  · intro T x y hxy
    have hx₀ : (x ≫ first f) ≫ f = y ≫ b := by simpa only [Category.assoc] using hxy
    have hx₁ : (x ≫ second f) ≫ f = y ≫ b := by
      simpa only [Category.assoc,← edge_condition f] using hxy
    let x₀ := H.lift (x ≫ first f) y hx₀
    let x₁ := H.lift (x ≫ second f) y hx₁
    have he : x₀ ≫ g = x₁ ≫ g := by simp only [x₀,x₁,IsPullback.lift_snd]
    refine ⟨pullback.lift x₀ x₁ he,?_,?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc,double_first,← Category.assoc,pullback.lift_fst]
        exact H.lift_fst _ _ _
      · rw [Category.assoc,double_second,← Category.assoc,pullback.lift_snd]
        exact H.lift_fst _ _ _
    · simp only [← Category.assoc,pullback.lift_fst,x₀,IsPullback.lift_snd]

include H in
lemma openImmersion [IsOpenImmersion b] : IsOpenImmersion (doubleMap f g a b h) :=
  MorphismProperty.of_isPullback (isPullback f g a b h H).flip
    (inferInstance : IsOpenImmersion b)
end ActualDoubleCartesian318
