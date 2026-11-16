module
public import SquareZeroRingLift318
public import DualNumberCocycleNaturality318
public import OriginalAffineThickeningFrames318
public section
noncomputable section
namespace OriginalDualSectionLift318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R)
/-- Canonical section map on the ACTUAL thickening, using its original first
projection and the original epsilon from its second projection. -/
@[expose] def lift : SquareZeroUnit318.Dual Γ(X,⊤) →+* Γ(thickening R p,⊤) :=
  SquareZeroRingLift318.lift (pullback.fst p (structureMap R)).appTop.hom
    (DualNumberInfinitesimalLines318.epsilon R p) (DualNumberInfinitesimalLines318.epsilon_square R p)
lemma reduction_lift (x : SquareZeroUnit318.Dual Γ(X,⊤)) :
    (reduction R p).appTop (lift R p x) = x.fst := by
  change (reduction R p).appTop
    ((pullback.fst p (structureMap R)).appTop x.fst +
      DualNumberInfinitesimalLines318.epsilon R p * (pullback.fst p (structureMap R)).appTop x.snd) = _
  rw [map_add, map_mul, DualNumberInfinitesimalLines318.reduction_epsilon, zero_mul, add_zero]
  change ((pullback.fst p (structureMap R)).appTop ≫ (reduction R p).appTop) x.fst = _
  rw [← Scheme.Hom.comp_appTop, reduction_fst]
  simp
variable {Y : Scheme.{u}} (q : Y ⟶ base R) (f : X ⟶ Y) (hf : f ≫ q = p)
lemma coefficient_naturality (a : Γ(Y,⊤)) :
    (map R p q f hf).appTop ((pullback.fst q (structureMap R)).appTop a) =
      (pullback.fst p (structureMap R)).appTop (f.appTop a) := by
  change ((pullback.fst q (structureMap R)).appTop ≫ (map R p q f hf).appTop) a =
    (f.appTop ≫ (pullback.fst p (structureMap R)).appTop) a
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
  rw [show map R p q f hf ≫ pullback.fst q (structureMap R) =
      pullback.fst p (structureMap R) ≫ f from RelativeLineFunctorPullback318.baseMap_fst p q f hf _]
/-- Original scheme functoriality changes both dual coordinates by the actual
section map, and preserves the actual nilpotent parameter. -/
lemma naturality (x : SquareZeroUnit318.Dual Γ(Y,⊤)) :
    (map R p q f hf).appTop (lift R q x) =
      lift R p (SquareZeroUnit318.map Γ(Y,⊤) f.appTop.hom x) := by
  change (map R p q f hf).appTop
    ((pullback.fst q (structureMap R)).appTop x.fst +
      DualNumberInfinitesimalLines318.epsilon R q * (pullback.fst q (structureMap R)).appTop x.snd) = _
  rw [map_add, map_mul, DualNumberCocycleNaturality318.epsilon_naturality,
    coefficient_naturality, coefficient_naturality]
  all_goals
    simp only [lift, SquareZeroRingLift318.lift_apply, SquareZeroUnit318.map_fst,
      SquareZeroUnit318.map_snd]
end OriginalDualSectionLift318
