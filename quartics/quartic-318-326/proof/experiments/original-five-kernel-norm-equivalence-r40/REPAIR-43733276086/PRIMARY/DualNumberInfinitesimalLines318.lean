module
public import DualNumberScheme318
public import UnitCocyclePointedLine318
public section
noncomputable section
namespace DualNumberInfinitesimalLines318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318
universe u
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R]
/-- The actual dual-number coordinate as a global section of Spec(R[epsilon]). -/
@[expose] def testEpsilon : Γ(test R,⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (SquareZeroUnit318.Dual R))).inv (TrivSqZeroExt.inr 1)
lemma testEpsilon_square : testEpsilon R * testEpsilon R = 0 := by
  unfold testEpsilon
  rw [← map_mul]
  simp
lemma zero_testEpsilon : (zero R).appTop (testEpsilon R) = 0 := by
  have h := congrArg (fun f => f (TrivSqZeroExt.inr (1 : R)))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (reductionRing R)))
  have hh := h.symm
  change (zero R).appTop (testEpsilon R) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv (reductionRing R (TrivSqZeroExt.inr 1)) at hh
  simpa [reductionRing] using hh
variable {X : Scheme.{u}} (p : X ⟶ base R)
/-- The coordinate on the actual fiber product, through its actual second projection. -/
@[expose] def epsilon : Γ(thickening R p,⊤) :=
  (pullback.snd p (structureMap R)).appTop (testEpsilon R)
lemma epsilon_square : epsilon R p * epsilon R p = 0 := by
  rw [epsilon, ← map_mul, testEpsilon_square, map_zero]
lemma reduction_epsilon : (reduction R p).appTop (epsilon R p) = 0 := by
  change ((pullback.snd p (structureMap R)).appTop ≫ (reduction R p).appTop) (testEpsilon R) = 0
  rw [← Scheme.Hom.comp_appTop, reduction_snd, Scheme.Hom.comp_appTop]
  change p.appTop ((zero R).appTop (testEpsilon R)) = 0
  rw [zero_testEpsilon, map_zero]
/-- Vanishing on the special fiber holds on EVERY original open, by the actual
structure-presheaf naturality square, not just on global or generic sections. -/
lemma reduction_epsilon_open (V : (thickening R p).Opens) :
    (reduction R p).app V
      (InfinitesimalUnitCocycle318.epsilon (thickening R p) (epsilon R p) V) = 0 := by
  have hn := congrArg (fun f => f (epsilon R p))
    ((reduction R p).c.naturality (homOfLE (show V ≤ ⊤ from le_top)).op)
  change (reduction R p).app V
      (InfinitesimalUnitCocycle318.epsilon (thickening R p) (epsilon R p) V) =
    X.presheaf.map (homOfLE (show (reduction R p) ⁻¹ᵁ V ≤ ⊤ from le_top)).op
      ((reduction R p).appTop (epsilon R p)) at hn
  rw [reduction_epsilon, map_zero] at hn
  exact hn
variable {ι : Type u} (U : ι → (thickening R p).Opens)
    (hc : (⊤ : (thickening R p).Opens) ≤ ⨆ a, U a)
/-- A complete additive cocycle produces an actual pointed line on the actual
square-zero thickening, with the special-fiber trivialization CONSTRUCTED. -/
@[expose] def deformation
    (c : InfinitesimalUnitCocycle318.AdditiveCocycle (thickening R p) U) :
    DualNumberScheme318.Deformation R p :=
  UnitCocyclePointedLine318.infinitesimal (reduction R p) U hc (epsilon R p)
    (epsilon_square R p) c (reduction_epsilon_open R p)
lemma underlying_object
    (c : InfinitesimalUnitCocycle318.AdditiveCocycle (thickening R p) U) :
    (deformation R p U hc c).line.object =
      CocycleModule318.object U
        (InfinitesimalUnitCocycle318.cocycle (thickening R p) (epsilon R p)
          (epsilon_square R p) U c) := rfl
lemma special_fiber_trivial
    (c : InfinitesimalUnitCocycle318.AdditiveCocycle (thickening R p) U) :
    LineSheafPullback318.pullback (reduction R p)
      (LineSheafClass318.classOf (deformation R p U hc c).line) =
        LineSheafUnit318.unitClass X :=
  LineSheafClass318.classOf_eq (deformation R p U hc c).trivialization
end DualNumberInfinitesimalLines318
