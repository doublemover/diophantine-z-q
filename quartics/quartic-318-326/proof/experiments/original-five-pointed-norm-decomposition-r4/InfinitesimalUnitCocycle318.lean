module
public import SquareZeroUnit318
public import CocycleCanonicalTransitions318
public import CocycleGaugeIso318
public import LineSheafClass318
public section
noncomputable section
namespace InfinitesimalUnitCocycle318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]
/-- The actual unit in an arbitrary original ring with a specified square-zero element. -/
@[expose] def infinitesimal (e : R) (he : e * e = 0) (a : R) : Rˣ where
  val := 1 + e * a
  inv := 1 - e * a
  val_inv := by
    calc
      (1 + e * a) * (1 - e * a) = 1 - (e * e) * (a * a) := by ring
      _ = 1 := by rw [he]; ring
  inv_val := by
    calc
      (1 - e * a) * (1 + e * a) = 1 - (e * e) * (a * a) := by ring
      _ = 1 := by rw [he]; ring
lemma infinitesimal_add (e : R) (he : e * e = 0) (a b : R) :
    infinitesimal e he (a + b) = infinitesimal e he a * infinitesimal e he b := by
  apply Units.ext
  change 1 + e * (a + b) = (1 + e * a) * (1 + e * b)
  calc
    1 + e * (a + b) = 1 + e * a + e * b + (e * e) * (a * b) := by rw [he]; ring
    _ = _ := by ring
@[simp] lemma infinitesimal_zero (e : R) (he : e * e = 0) : infinitesimal e he 0 = 1 := by
  apply Units.ext
  simp [infinitesimal]
lemma infinitesimal_neg (e : R) (he : e * e = 0) (a : R) :
    infinitesimal e he (-a) = (infinitesimal e he a)⁻¹ := by
  apply Units.ext
  change 1 + e * (-a) = 1 - e * a
  ring
variable (X : Scheme.{u})
@[expose] def restrict {V W : X.Opens} (h : V ≤ W) : Γ(X,W) →+* Γ(X,V) :=
  (X.presheaf.map (homOfLE h).op).hom
lemma restrict_trans {V W T : X.Opens} (h : V ≤ W) (k : W ≤ T) (a : Γ(X,T)) :
    restrict X h (restrict X k a) = restrict X (h.trans k) a := by
  have hh := congrArg (fun f : X.presheaf.obj (op T) ⟶ X.presheaf.obj (op V) => f a)
    (X.presheaf.map_comp (homOfLE k).op (homOfLE h).op)
  exact hh.symm
variable (e : Γ(X,⊤)) (he : e * e = 0)
@[expose] def epsilon (V : X.Opens) : Γ(X,V) := restrict X le_top e
include he in
lemma epsilon_square (V : X.Opens) : epsilon X e V * epsilon X e V = 0 := by
  rw [epsilon, ← map_mul, he, map_zero]
@[expose] def unit (V : X.Opens) (a : Γ(X,V)) : Γ(X,V)ˣ :=
  infinitesimal (epsilon X e V) (epsilon_square X e he V) a
lemma unit_restrict {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)) :
    Units.map (restrict X h).toMonoidHom (unit X e he W a) =
      unit X e he V (restrict X h a) := by
  apply Units.ext
  change restrict X h (1 + epsilon X e W * a) = 1 + epsilon X e V * restrict X h a
  rw [map_add, map_one, map_mul]
  congr 1
  congr 1
  exact restrict_trans X h le_top e
variable {ι : Type u} (U : ι → X.Opens)
/-- Additive data on all original double and triple intersections. -/
structure AdditiveCocycle where
  transition : ∀ i j, Γ(X,U i ⊓ U j)
  diagonal : ∀ i, transition i i = 0
  triple : ∀ i j k,
    restrict X inf_le_left (transition i j) +
      restrict X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (transition j k) =
    restrict X (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (transition i k)
/-- The actual 1+epsilon cocycle in the existing structure-units sheaf. -/
@[expose] def cocycle (c : AdditiveCocycle X U) :
    UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U where
  transition i j := unit X e he _ (c.transition i j)
  diagonal i := by rw [c.diagonal]; exact infinitesimal_zero _ _
  triple i j k := by
    change Units.map (restrict X inf_le_left).toMonoidHom _ *
      Units.map (restrict X (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).toMonoidHom _ =
      Units.map (restrict X (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).toMonoidHom _
    rw [unit_restrict, unit_restrict, unit_restrict]
    change infinitesimal _ _ _ * infinitesimal _ _ _ = infinitesimal _ _ _
    rw [← infinitesimal_add, c.triple]
/-- These are genuine rank-one locally framed sheaves, not merely cocycle labels. -/
@[expose] def line (c : AdditiveCocycle X U) (hc : (⊤ : X.Opens) ≤ ⨆ i, U i) :
    LineSheafClass318.Line X where
  object := CocycleModule318.object U (cocycle X e he U c)
  Index := ι
  opens := U
  cover := hc
  frame := CocycleCanonicalTransitions318.frames U (cocycle X e he U c)
lemma original_transitions (c : AdditiveCocycle X U) :
    LineFrameCocycle318.cocycle (CocycleModule318.object U (cocycle X e he U c)) U
      (CocycleCanonicalTransitions318.frames U (cocycle X e he U c)) = cocycle X e he U c :=
  CocycleCanonicalTransitions318.cocycle_eq U _
/-- Exact additive coboundary sign matches the repository's actual multiplicative gauge. -/
lemma gauge_equation (c d : AdditiveCocycle X U) (a : ∀ i, Γ(X,U i))
    (h : ∀ i j, d.transition i j = restrict X inf_le_left (a i) -
      restrict X inf_le_right (a j) + c.transition i j) (i j : ι) :
    (cocycle X e he U d).transition i j =
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units X).obj U
        (fun i => unit X e he (U i) (a i)) i j * (cocycle X e he U c).transition i j := by
  have hu : unit X e he (U i ⊓ U j) (d.transition i j) =
      (Units.map (restrict X (show U i ⊓ U j ≤ U i from inf_le_left)).toMonoidHom
        (unit X e he (U i) (a i)) *
      (Units.map (restrict X (show U i ⊓ U j ≤ U j from inf_le_right)).toMonoidHom
        (unit X e he (U j) (a j)))⁻¹) *
      unit X e he (U i ⊓ U j) (c.transition i j) := by
    rw [unit_restrict, unit_restrict, h]
    dsimp only [unit]
    rw [← infinitesimal_neg, ← infinitesimal_add, ← infinitesimal_add]
    congr 1
    ring
  exact hu
/-- The original gauge producer now gives an isomorphism of actual 1+epsilon lines. -/
@[expose] def gaugeIso (c d : AdditiveCocycle X U) (hc : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (a : ∀ i, Γ(X,U i))
    (h : ∀ i j, d.transition i j = restrict X inf_le_left (a i) -
      restrict X inf_le_right (a j) + c.transition i j) :
    (line X e he U c hc).object ≅ (line X e he U d hc).object :=
  CocycleGaugeIso318.iso U (cocycle X e he U c) (cocycle X e he U d)
    (fun i => unit X e he (U i) (a i)) (gauge_equation X e he U c d a h)
end InfinitesimalUnitCocycle318
