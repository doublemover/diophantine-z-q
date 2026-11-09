module
public import InfinitesimalPointedGauge318
public section
noncomputable section
namespace AdditiveDeformationClasses318
open AlgebraicGeometry CategoryTheory InfinitesimalUnitCocycle318
universe u
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
/-- Original full-cover additive coboundaries, with the checked gauge sign. -/
@[expose] def Related (c d : AdditiveCocycle X U) : Prop :=
  ∃ a : ∀ k, Γ(X,U k), ∀ k l, d.transition k l = restrict X inf_le_left (a k) -
    restrict X inf_le_right (a l) + c.transition k l
lemma related_refl (c : AdditiveCocycle X U) : Related X U c c := by
  refine ⟨fun _ => 0, ?_⟩
  intro k l
  simp
lemma related_symm {c d : AdditiveCocycle X U} (h : Related X U c d) : Related X U d c := by
  obtain ⟨a,ha⟩ := h
  refine ⟨fun k => -a k, ?_⟩
  intro k l
  rw [map_neg, map_neg, ha k l]
  ring
lemma related_trans {c d f : AdditiveCocycle X U} (h : Related X U c d)
    (h' : Related X U d f) : Related X U c f := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := h'
  refine ⟨fun k => a k + b k, ?_⟩
  intro k l
  rw [map_add, map_add, hb k l, ha k l]
  ring
@[expose] def additiveSetoid : Setoid (AdditiveCocycle X U) where
  r := Related X U
  iseqv := ⟨related_refl X U, related_symm X U, related_trans X U⟩
abbrev Classes := Quotient (additiveSetoid X U)
variable {X} {X₀ : Scheme.{u}} (i : X₀ ⟶ X)
    (hc : (⊤ : X.Opens) ≤ ⨆ a, U a) (e : Γ(X,⊤)) (he : e * e = 0)
    (hz : ∀ V : X.Opens, i.app V (epsilon X e V) = 0)
/-- A well-defined map from additive cocycle classes to ACTUAL pointed line
classes, proved using the actual original gauge isomorphism and its frame square. -/
@[expose] def toPointed : Classes X U → PointedLineDeformation318.Class i :=
  Quotient.lift (fun c => PointedLineDeformation318.classOf i
    (UnitCocyclePointedLine318.infinitesimal i U hc e he c hz)) (by
      intro c d h
      obtain ⟨a,ha⟩ := h
      exact InfinitesimalPointedGauge318.class_eq i U hc e he hz c d a ha)
lemma toPointed_mk (c : AdditiveCocycle X U) :
    toPointed U i hc e he hz (Quotient.mk _ c) =
      PointedLineDeformation318.classOf i
        (UnitCocyclePointedLine318.infinitesimal i U hc e he c hz) := rfl
variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ DualNumberScheme318.base R)
    {κ : Type u} (V : κ → (DualNumberScheme318.thickening R p).Opens)
    (hV : (⊤ : (DualNumberScheme318.thickening R p).Opens) ≤ ⨆ k, V k)
/-- The square-zero scheme specialization discharges epsilon and reduction
hypotheses from their actual geometric construction. This is not yet an H1 equivalence. -/
@[expose] def dualNumberClasses :
    Classes (DualNumberScheme318.thickening R p) V → DualNumberScheme318.Class R p :=
  toPointed V (DualNumberScheme318.reduction R p) hV
    (DualNumberInfinitesimalLines318.epsilon R p) (DualNumberInfinitesimalLines318.epsilon_square R p)
    (DualNumberInfinitesimalLines318.reduction_epsilon_open R p)
lemma dualNumberClasses_mk
    (c : AdditiveCocycle (DualNumberScheme318.thickening R p) V) :
    dualNumberClasses p V hV (Quotient.mk _ c) =
      PointedLineDeformation318.classOf (DualNumberScheme318.reduction R p)
        (DualNumberInfinitesimalLines318.deformation R p V hV c) := rfl
end AdditiveDeformationClasses318
