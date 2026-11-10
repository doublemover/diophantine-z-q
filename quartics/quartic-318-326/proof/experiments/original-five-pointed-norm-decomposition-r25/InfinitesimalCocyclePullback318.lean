module
public import OriginalCocyclePullbackLine318
public section
noncomputable section
namespace InfinitesimalCocyclePullback318
open AlgebraicGeometry CategoryTheory Opposite InfinitesimalUnitCocycle318
universe u
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (eY : Γ(Y,⊤)) (eX : Γ(X,⊤))
    (heY : eY * eY = 0) (heX : eX * eX = 0) (he : f.appTop eY = eX)
include he in
lemma epsilon_appLE (W : Y.Opens) (W' : X.Opens) (hW : W' ≤ f ⁻¹ᵁ W) :
    f.appLE W W' hW (epsilon Y eY W) = epsilon X eX W' := by
  have hs : Y.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op ≫ f.appLE W W' hW =
      f.appTop ≫ X.presheaf.map (homOfLE (show W' ≤ ⊤ from le_top)).op := by
    calc
      _ = f.appLE ⊤ W' (show W' ≤ f ⁻¹ᵁ ⊤ from le_top) := by rw [Scheme.Hom.map_appLE]
      _ = _ := rfl
  have h := congrArg (fun k => k eY) hs
  change f.appLE W W' hW (epsilon Y eY W) = restrict X le_top (f.appTop eY) at h
  change f.appLE W W' hW (epsilon Y eY W) = restrict X le_top eX
  exact h.trans (congrArg (restrict X (show W' ≤ ⊤ from le_top)) he)
variable {ι : Type u} (U : ι → Y.Opens) (V : ι → X.Opens) (hV : ∀ a, V a ≤ f ⁻¹ᵁ U a)
include he in
/-- Pullback of the actual1+epsilon transition is exactly1+epsilon times the
actual additive coefficient pullback, including every original restriction. -/
lemma cocycle_eq (c : AdditiveCocycle Y U) :
    UnitCocycleSchemeRefinement318.cocycle f U V hV (cocycle Y eY heY U c) =
      cocycle X eX heX V (AdditiveCocycleRefinement318.cocycle f U V hV c) := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro a b
  apply Units.ext
  change f.appLE (U a ⊓ U b) (V a ⊓ V b) _ (1 + epsilon Y eY _ * c.transition a b) =
    1 + epsilon X eX _ * f.appLE (U a ⊓ U b) (V a ⊓ V b) _ (c.transition a b)
  rw [map_add, map_one, map_mul, epsilon_appLE f eY eX he]
/-- A genuine iso from the original pulled infinitesimal line to the original
coefficient-pulled infinitesimal line on any complete source-cover refinement. -/
@[expose] def iso (c : AdditiveCocycle Y U) (hc : (⊤ : X.Opens) ≤ ⨆ a, V a) :
    (Scheme.Modules.pullback f).obj (CocycleModule318.object U (cocycle Y eY heY U c)) ≅
      CocycleModule318.object V
        (cocycle X eX heX V (AdditiveCocycleRefinement318.cocycle f U V hV c)) :=
  OriginalCocyclePullbackLine318.iso f U (cocycle Y eY heY U c) V hV hc ≪≫
    CocycleEqualityTransport318.iso V (cocycle_eq f eY eX heY heX he U V hV c)
end InfinitesimalCocyclePullback318
