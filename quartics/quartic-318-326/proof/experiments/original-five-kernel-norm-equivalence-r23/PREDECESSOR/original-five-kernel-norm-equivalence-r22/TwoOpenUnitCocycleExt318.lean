module
public import OriginalOpenUnitLogarithm318
public import UnitCocycleSubopens318
public section
noncomputable section
namespace TwoOpenUnitCocycleExt318
open CategoryTheory Opposite TopologicalSpace UnitTransitionCocycle318
universe u
variable {X : TopCat.{u}} {F : X.Presheaf CommGrpCat.{u}} (U : Bool → Opens X)
lemma restrict_refl {W : Opens X} (a : F.obj (op W)) :
    restrict F (show W ≤ W from le_rfl) a = a := by
  change F.map (𝟙 (op W)) a = a
  rw [F.map_id]
  all_goals rfl
lemma reverse (c : Cocycle F U) : c.transition true false =
    (restrict F (show U true ⊓ U false ≤ U false ⊓ U true from
      le_inf inf_le_right inf_le_left) (c.transition false true))⁻¹ := by
  have h := UnitCocycleSubopens318.transition_reverse c false true
    (show U true ⊓ U false ≤ U false from inf_le_right)
    (show U true ⊓ U false ≤ U true from inf_le_left)
  rw [restrict_refl] at h
  exact h
/-- All four transitions, including the reverse and both diagonal edges,
are fixed by the single original forward overlap unit. -/
lemma ext (c d : Cocycle F U) (h : c.transition false true = d.transition false true) : c = d := by
  apply Cocycle.ext
  intro k l
  cases k <;> cases l
  · exact (c.diagonal false).trans (d.diagonal false).symm
  · exact h
  · rw [reverse, reverse, h]
  · exact (c.diagonal true).trans (d.diagonal true).symm
end TwoOpenUnitCocycleExt318
