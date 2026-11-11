module
public import UnitTransitionCocycle318
public section
noncomputable section
namespace UnitCocycleSubopens318
open CategoryTheory Opposite TopologicalSpace UnitTransitionCocycle318
universe u v
variable {X : TopCat.{u}} {ι : Type v} {F : X.Presheaf CommGrpCat.{u}}
set_option maxHeartbeats 200000

/-- The original presheaf restriction through a common intermediate open. -/
lemma restrict_restrict {V W Z : Opens X} (h : V ≤ W) (k : W ≤ Z)
    (s : F.obj (op Z)) :
    restrict F h (restrict F k s) = restrict F (h.trans k) s := by
  change ((F.map (homOfLE k).op ≫ F.map (homOfLE h).op) :
    F.obj (op Z) ⟶ F.obj (op V)) s = _
  rw [← F.map_comp]
  rfl

variable {U : ι → Opens X} (c : Cocycle F U)

/-- The actual cocycle identity on any original common subopen, not only
on the entire standard triple intersection. -/
lemma transition_mul (i j k : ι) {W : Opens X}
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    restrict F (le_inf hi hj) (c.transition i j) *
      restrict F (le_inf hj hk) (c.transition j k) =
    restrict F (le_inf hi hk) (c.transition i k) := by
  have h := congrArg (restrict F (le_inf (le_inf hi hj) hk)) (c.triple i j k)
  simpa only [map_mul, restrict_restrict] using h

lemma transition_diagonal (i : ι) {W : Opens X} (hi : W ≤ U i) :
    restrict F (le_inf hi hi) (c.transition i i) = 1 := by
  rw [c.diagonal, map_one]

/-- Reversing the two indices yields the actual multiplicative inverse
on every common subopen, including the empty open. -/
lemma transition_mul_reverse (i j : ι) {W : Opens X}
    (hi : W ≤ U i) (hj : W ≤ U j) :
    restrict F (le_inf hi hj) (c.transition i j) *
      restrict F (le_inf hj hi) (c.transition j i) = 1 := by
  rw [transition_mul c i j i hi hj hi, transition_diagonal c i hi]

lemma transition_reverse (i j : ι) {W : Opens X}
    (hi : W ≤ U i) (hj : W ≤ U j) :
    restrict F (le_inf hj hi) (c.transition j i) =
      (restrict F (le_inf hi hj) (c.transition i j))⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (transition_mul_reverse c i j hi hj)

end UnitCocycleSubopens318
