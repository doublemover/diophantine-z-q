module
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.Presheaf
public section
noncomputable section
namespace UnitTransitionCocycle318
open CategoryTheory Opposite TopologicalSpace
universe u v
variable {X : TopCat.{u}} {ι : Type v}
set_option maxHeartbeats 300000
/-- Restriction in the actual commutative-group presheaf. -/
@[expose] def restrict (F : X.Presheaf CommGrpCat.{u}) {V W : Opens X} (h : V ≤ W) :
    F.obj (op W) →* F.obj (op V) := (F.map (homOfLE h).op).hom
/-- The actual naturality square, evaluated on a section. -/
lemma restrict_map {F G : X.Presheaf CommGrpCat.{u}} (a : F ⟶ G)
    {V W : Opens X} (h : V ≤ W) (s : F.obj (op W)) :
    restrict G h (a.app (op W) s) = a.app (op V) (restrict F h s) := by
  exact (congrArg (fun k : F.obj (op W) ⟶ G.obj (op V) => k s)
    (a.naturality (homOfLE h).op)).symm
/-- Transition functions with identities on every complete double and triple
intersection. No refinement or line-bundle descent is built into this data. -/
structure Cocycle (F : X.Presheaf CommGrpCat.{u}) (U : ι → Opens X) where
  transition : ∀ i j, F.obj (op (U i ⊓ U j))
  diagonal : ∀ i, transition i i = 1
  triple : ∀ i j k,
    restrict F inf_le_left (transition i j) *
      restrict F (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (transition j k) =
    restrict F (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (transition i k)
@[ext] lemma Cocycle.ext {F : X.Presheaf CommGrpCat.{u}} {U : ι → Opens X}
    {c d : Cocycle F U} (h : ∀ i j, c.transition i j = d.transition i j) : c = d := by
  cases c with
  | mk ct cd cc =>
    cases d with
    | mk dt dd dc =>
      have heq : ct = dt := funext fun i => funext (h i)
      cases heq
      rfl
/-- A presheaf homomorphism transports actual unit transition cocycles. -/
@[expose] def map {F G : X.Presheaf CommGrpCat.{u}} (a : F ⟶ G)
    {U : ι → Opens X} (c : Cocycle F U) : Cocycle G U where
  transition i j := a.app (op (U i ⊓ U j)) (c.transition i j)
  diagonal i := by rw [c.diagonal]; exact map_one (a.app _).hom
  triple i j k := by
    rw [restrict_map, restrict_map, restrict_map, ← map_mul]
    exact congrArg (fun s => a.app (op ((U i ⊓ U j) ⊓ U k)) s) (c.triple i j k)
/-- A change of trivialization contributes this actual unit coboundary. -/
@[expose] def coboundary (F : X.Presheaf CommGrpCat.{u}) (U : ι → Opens X)
    (a : ∀ i, F.obj (op (U i))) (i j : ι) : F.obj (op (U i ⊓ U j)) :=
  restrict F inf_le_left (a i) * (restrict F inf_le_right (a j))⁻¹
lemma map_coboundary {F G : X.Presheaf CommGrpCat.{u}} (a : F ⟶ G)
    (U : ι → Opens X) (s : ∀ i, F.obj (op (U i))) (i j : ι) :
    a.app (op (U i ⊓ U j)) (coboundary F U s i j) =
      coboundary G U (fun k => a.app (op (U k)) (s k)) i j := by
  simp only [coboundary, map_mul, map_inv, restrict_map]
/-- Explicit change-of-trivialization relation, without claiming a Picard
classification or that all source bundles admit the chosen cover. -/
@[expose] def GaugeEquivalent {F : X.Presheaf CommGrpCat.{u}} {U : ι → Opens X}
    (c d : Cocycle F U) : Prop :=
  ∃ a : ∀ i, F.obj (op (U i)), ∀ i j,
    d.transition i j = coboundary F U a i j * c.transition i j
lemma map_gaugeEquivalent {F G : X.Presheaf CommGrpCat.{u}} (a : F ⟶ G)
    {U : ι → Opens X} {c d : Cocycle F U} (h : GaugeEquivalent c d) :
    GaugeEquivalent (map a c) (map a d) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨fun k => a.app (op (U k)) (s k), ?_⟩
  intro i j
  change a.app (op (U i ⊓ U j)) (d.transition i j) = _
  rw [hs, map_mul, map_coboundary]
  rfl
end UnitTransitionCocycle318
