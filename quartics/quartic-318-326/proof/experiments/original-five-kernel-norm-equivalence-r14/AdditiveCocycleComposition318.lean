module
public import DualNumberCocycleNaturality318
public section
noncomputable section
namespace AdditiveCocycleComposition318
open AlgebraicGeometry CategoryTheory InfinitesimalUnitCocycle318
universe u
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[ext] lemma ext {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    {c d : AdditiveCocycle X U} (h : ∀ a b, c.transition a b = d.transition a b) : c = d := by
  cases c with
  | mk ct cd cc =>
    cases d with
    | mk dt dd dc =>
      have ht : ct = dt := funext fun a => funext (h a)
      cases ht
      rfl
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {ι : Type u}
    (U : ι → Z.Opens) (V : ι → Y.Opens) (W : ι → X.Opens)
    (hV : ∀ a, V a ≤ g ⁻¹ᵁ U a) (hW : ∀ a, W a ≤ f ⁻¹ᵁ V a)
/-- Composition retains the original scheme coefficient maps on every complete
refinement intersection. The composite containment is the actual pulled one. -/
lemma comp (c : AdditiveCocycle Z U) :
    AdditiveCocycleRefinement318.cocycle f V W hW
      (AdditiveCocycleRefinement318.cocycle g U V hV c) =
    AdditiveCocycleRefinement318.cocycle (f ≫ g) U W
      (fun a => (hW a).trans (f.preimage_mono (hV a))) c := by
  apply ext
  intro a b
  change f.appLE (V a ⊓ V b) (W a ⊓ W b) _
    (g.appLE (U a ⊓ U b) (V a ⊓ V b) _ (c.transition a b)) = _
  exact congrArg (fun k => k (c.transition a b))
    (Scheme.Hom.appLE_comp_appLE f g (U a ⊓ U b) (V a ⊓ V b) (W a ⊓ W b)
      (inf_le_inf (hV a) (hV b)) (inf_le_inf (hW a) (hW b)))
/-- Equality of the original scheme maps transports their coefficient cocycles;
only containment proofs change, not a chosen section-ring equivalence. -/
lemma congr_map {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {ι : Type u}
    (U : ι → Y.Opens) (V : ι → X.Opens)
    (hf : ∀ a, V a ≤ f ⁻¹ᵁ U a) (hg : ∀ a, V a ≤ g ⁻¹ᵁ U a)
    (c : AdditiveCocycle Y U) :
    AdditiveCocycleRefinement318.cocycle f U V hf c =
      AdditiveCocycleRefinement318.cocycle g U V hg c := by
  subst g
  rfl
end AdditiveCocycleComposition318
