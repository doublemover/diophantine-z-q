module
public import AdditiveCocycleComposition318
public section
noncomputable section
namespace TwoOpenCocycleNaturality318
open AlgebraicGeometry CategoryTheory InfinitesimalUnitCocycle318 TwoOpenAdditiveCocycle318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U V : Y.Opens) (W Z : X.Opens)
    (hW : W ≤ f ⁻¹ᵁ U) (hZ : Z ≤ f ⁻¹ᵁ V)
@[expose] def coverLE : ∀ a, opens W Z a ≤ f ⁻¹ᵁ opens U V a
  | false => hW
  | true => hZ
/-- All four original two-cover transitions pull through the actual overlap
map, with the original forward/reverse sign and genuine restriction square. -/
lemma cocycle (x : Γ(Y,U ⊓ V)) :
    AdditiveCocycleRefinement318.cocycle f (opens U V) (opens W Z) (coverLE f U V W Z hW hZ)
      (TwoOpenAdditiveCocycle318.cocycle U V x) =
    TwoOpenAdditiveCocycle318.cocycle W Z (f.appLE (U ⊓ V) (W ⊓ Z) (inf_le_inf hW hZ) x) := by
  apply AdditiveCocycleComposition318.ext
  intro a b
  cases a <;> cases b
  · simp [AdditiveCocycleRefinement318.cocycle, TwoOpenAdditiveCocycle318.cocycle,
      transition]
  · change f.appLE (U ⊓ V) (W ⊓ Z) _
      ((TwoOpenAdditiveCocycle318.cocycle U V x).transition false true) =
        (TwoOpenAdditiveCocycle318.cocycle W Z _).transition false true
    rw [forward, forward]
  · change f.appLE (V ⊓ U) (Z ⊓ W) _ (transition U V x true false) =
      transition W Z (f.appLE (U ⊓ V) (W ⊓ Z) (inf_le_inf hW hZ) x) true false
    simp only [transition, Bool.true_eq_false, ↓reduceDIte, ↓reduceIte, map_neg]
    exact congrArg Neg.neg
      (AdditiveCocycleRefinement318.restrict_appLE f
        (pair_le U V true false (by decide))
        (pair_le W Z true false (by decide))
        (inf_le_inf hZ hW) (inf_le_inf hW hZ) x).symm
  · simp [AdditiveCocycleRefinement318.cocycle, TwoOpenAdditiveCocycle318.cocycle,
      transition]
end TwoOpenCocycleNaturality318
