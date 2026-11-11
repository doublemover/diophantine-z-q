module
public import OriginalFiveHOnePointedNaturality318
public section
noncomputable section
namespace AdditiveCocycleSum318
open AlgebraicGeometry CategoryTheory InfinitesimalUnitCocycle318
universe u
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
/-- Addition uses every original overlap, before either exponentiation or gluing. -/
@[expose] def add (c d : AdditiveCocycle X U) : AdditiveCocycle X U where
  transition i j := c.transition i j + d.transition i j
  diagonal i := by rw [c.diagonal, d.diagonal, add_zero]
  triple i j k := by
    simp only [map_add]
    calc
      _ = (restrict X inf_le_left (c.transition i j) +
          restrict X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c.transition j k)) +
        (restrict X inf_le_left (d.transition i j) +
          restrict X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (d.transition j k)) := by abel
      _ = _ := by rw [c.triple, d.triple]
variable {Y : Scheme.{u}} (f : X ⟶ Y) (V : ι → Y.Opens)
    (hU : ∀ i, U i ≤ f ⁻¹ᵁ V i)
lemma pullback_add (c d : AdditiveCocycle Y V) :
    AdditiveCocycleRefinement318.cocycle f V U hU (add V c d) =
      add U (AdditiveCocycleRefinement318.cocycle f V U hU c)
        (AdditiveCocycleRefinement318.cocycle f V U hU d) := by
  apply AdditiveCocycleComposition318.ext
  intro i j
  exact (f.appLE (V i ⊓ V j) (U i ⊓ U j) _).hom.map_add _ _
lemma twoOpen_add {X : Scheme.{0}} (U V : X.Opens) (x y : Γ(X,U ⊓ V)) :
    TwoOpenAdditiveCocycle318.cocycle U V (x + y) =
      add (TwoOpenAdditiveCocycle318.opens U V)
        (TwoOpenAdditiveCocycle318.cocycle U V x) (TwoOpenAdditiveCocycle318.cocycle U V y) := by
  apply AdditiveCocycleComposition318.ext
  intro a b
  cases a <;> cases b <;>
    simp [TwoOpenAdditiveCocycle318.cocycle, TwoOpenAdditiveCocycle318.transition, add, map_add] <;> abel
end AdditiveCocycleSum318
