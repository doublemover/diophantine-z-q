module
public import UnitCocyclePointedGauge318
public import DualNumberInfinitesimalLines318
public section
noncomputable section
namespace InfinitesimalPointedGauge318
open AlgebraicGeometry CategoryTheory PointedLineDeformation318 InfinitesimalUnitCocycle318
universe u
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (hc : (⊤ : X.Opens) ≤ ⨆ a, U a) (e : Γ(X,⊤)) (he : e * e = 0)
    (hz : ∀ V : X.Opens, i.app V (epsilon X e V) = 0)
include hz in
lemma unit_reduces (V : X.Opens) (a : Γ(X,V)) : i.app V (unit X e he V a).val = 1 := by
  change i.app V (1 + epsilon X e V * a) = 1
  rw [map_add, map_one, map_mul, hz, zero_mul, add_zero]
include hz in
lemma reduces (c : AdditiveCocycle X U) :
    UnitCocyclePointedLine318.ReducesToOne i U (cocycle X e he U c) := by
  intro a b
  apply Units.ext
  exact unit_reduces i e he hz _ _
/-- The SAME original gauge sheaf isomorphism is now proved pointed. -/
@[expose] def pointedIso (c d : AdditiveCocycle X U) (a : ∀ k, Γ(X,U k))
    (hg : ∀ k l, d.transition k l = restrict X inf_le_left (a k) -
      restrict X inf_le_right (a l) + c.transition k l) :
    PointedIso i (UnitCocyclePointedLine318.infinitesimal i U hc e he c hz)
      (UnitCocyclePointedLine318.infinitesimal i U hc e he d hz) :=
  UnitCocyclePointedGauge318.pointedIso i U (cocycle X e he U c) (cocycle X e he U d)
    hc (reduces i U e he hz c) (reduces i U e he hz d)
    (fun k => unit X e he (U k) (a k)) (gauge_equation X e he U c d a hg)
    (fun k => unit_reduces i e he hz (U k) (a k))
lemma class_eq (c d : AdditiveCocycle X U) (a : ∀ k, Γ(X,U k))
    (hg : ∀ k l, d.transition k l = restrict X inf_le_left (a k) -
      restrict X inf_le_right (a l) + c.transition k l) :
    classOf i (UnitCocyclePointedLine318.infinitesimal i U hc e he c hz) =
      classOf i (UnitCocyclePointedLine318.infinitesimal i U hc e he d hz) :=
  (classOf_eq_iff i _ _).2 ⟨pointedIso i U hc e he hz c d a hg⟩
end InfinitesimalPointedGauge318
