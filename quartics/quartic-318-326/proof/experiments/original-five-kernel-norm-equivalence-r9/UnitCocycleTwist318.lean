module
public import PointedCocycleReductionGauge318
public import Mathlib.Tactic.Group
public section
noncomputable section
namespace UnitCocycleTwist318
open CategoryTheory Opposite TopologicalSpace UnitTransitionCocycle318
universe u v
set_option maxHeartbeats 1200000
variable {X : TopCat.{u}} {κ : Type v} (F : X.Presheaf CommGrpCat.{u}) (U : κ → Opens X)
lemma restrict_trans {V W T : Opens X} (h : V ≤ W) (k : W ≤ T) (a : F.obj (op T)) :
    restrict F h (restrict F k a) = restrict F (h.trans k) a := by
  exact (congrArg (fun f => f a) (F.map_comp (homOfLE k).op (homOfLE h).op)).symm
lemma gauge_mul {G : Type*} [CommGroup G] (a b c x y : G) :
    (a * b⁻¹ * x) * (b * c⁻¹ * y) = a * c⁻¹ * (x * y) := by
  calc
    (a * b⁻¹ * x) * (b * c⁻¹ * y) = (a * c⁻¹ * (x * y)) * (b⁻¹ * b) := by ac_rfl
    _ = a * c⁻¹ * (x * y) := by rw [inv_mul_cancel, mul_one]
/-- Actual change of the ENTIRE cocycle by the supplied original local units. -/
@[expose] def twist (c : Cocycle F U) (a : ∀ k, F.obj (op (U k))) : Cocycle F U where
  transition k l := coboundary F U a k l * c.transition k l
  diagonal k := by simp [coboundary, c.diagonal]
  triple k l m := by
    simp only [coboundary, map_mul, map_inv, restrict_trans]
    rw [gauge_mul, c.triple]
lemma equivalent (c : Cocycle F U) (a : ∀ k, F.obj (op (U k))) :
    GaugeEquivalent c (twist F U c a) := ⟨a, fun _ _ => rfl⟩
lemma map_twist {G : X.Presheaf CommGrpCat.{u}} (f : F ⟶ G)
    (c : Cocycle F U) (a : ∀ k, F.obj (op (U k))) :
    UnitTransitionCocycle318.map f (twist F U c a) =
      twist G U (UnitTransitionCocycle318.map f c) (fun k => f.app (op (U k)) (a k)) := by
  apply Cocycle.ext
  intro k l
  change f.app _ (coboundary F U a k l * c.transition k l) = _
  rw [map_mul, map_coboundary]
  all_goals rfl
end UnitCocycleTwist318
