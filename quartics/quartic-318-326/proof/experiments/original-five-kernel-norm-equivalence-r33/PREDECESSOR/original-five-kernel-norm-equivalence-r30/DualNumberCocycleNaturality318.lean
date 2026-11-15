module
public import InfinitesimalCocyclePullback318
public section
noncomputable section
namespace DualNumberCocycleNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318
universe u
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) (hf : f ≫ q = p)
/-- The actual thickened original map preserves the actual epsilon coordinate,
by the ORIGINAL second fiber-product projection square. -/
lemma epsilon_naturality : (map R p q f hf).appTop (DualNumberInfinitesimalLines318.epsilon R q) =
    DualNumberInfinitesimalLines318.epsilon R p := by
  change ((pullback.snd q (structureMap R)).appTop ≫ (map R p q f hf).appTop)
    (DualNumberInfinitesimalLines318.testEpsilon R) =
      (pullback.snd p (structureMap R)).appTop (DualNumberInfinitesimalLines318.testEpsilon R)
  rw [← Scheme.Hom.comp_appTop]
  rw [show map R p q f hf ≫ pullback.snd q (structureMap R) =
    pullback.snd p (structureMap R) from
      RelativeLineFunctorPullback318.baseMap_snd p q f hf (structureMap R)]
variable {ι : Type u} (U : ι → (thickening R q).Opens) (V : ι → (thickening R p).Opens)
    (hU : (⊤ : (thickening R q).Opens) ≤ ⨆ a, U a)
    (hV : (⊤ : (thickening R p).Opens) ≤ ⨆ a, V a)
    (hVU : ∀ a, V a ≤ map R p q f hf ⁻¹ᵁ U a)
/-- Naturality in ACTUAL pointed classes, using the original cocycle pullback
iso and the constructed split-reduction correction, rather than assuming a
comparison of independently chosen special-fiber frames. -/
lemma pointed_cocycle (c : InfinitesimalUnitCocycle318.AdditiveCocycle (thickening R q) U) :
    DualNumberScheme318.pullback R p q f hf
      (PointedLineDeformation318.classOf (reduction R q)
        (DualNumberInfinitesimalLines318.deformation R q U hU c)) =
      PointedLineDeformation318.classOf (reduction R p)
        (DualNumberInfinitesimalLines318.deformation R p V hV
          (AdditiveCocycleRefinement318.cocycle (map R p q f hf) U V hVU c)) := by
  change PointedLineDeformation318.classOf (reduction R p)
    (PointedLinePullback318.deformation (reduction R p) (reduction R q)
      (map R p q f hf) f (reduction_map R p q f hf)
      (DualNumberInfinitesimalLines318.deformation R q U hU c)) = _
  apply DualNumberPointedKernel318.class_eq_of_iso p
  exact InfinitesimalCocyclePullback318.iso (map R p q f hf)
    (DualNumberInfinitesimalLines318.epsilon R q) (DualNumberInfinitesimalLines318.epsilon R p)
    (DualNumberInfinitesimalLines318.epsilon_square R q) (DualNumberInfinitesimalLines318.epsilon_square R p)
    (epsilon_naturality p q f hf) U V hVU c hV
/-- Naturality descends through the original additive coboundary quotient on
all original covers and refinements, not just individual displayed cocycles. -/
lemma pointed_classes (c : AdditiveDeformationClasses318.Classes (thickening R q) U) :
    DualNumberScheme318.pullback R p q f hf
      (AdditiveDeformationClasses318.dualNumberClasses q U hU c) =
      AdditiveDeformationClasses318.dualNumberClasses p V hV
        (AdditiveCocycleRefinement318.classes (map R p q f hf) U V hVU c) := by
  induction c using Quotient.inductionOn with
  | h c => exact pointed_cocycle p q f hf U V hU hV hVU c
end DualNumberCocycleNaturality318
