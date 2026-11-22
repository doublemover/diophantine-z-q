module

public import CocycleCanonicalTransitions318
public import LineSheafClass318
public import Mathlib.Tactic.Ring

/-!
An additive cocycle of actual structure sections and one actual global
square-zero section produce the genuine invertible module sheaf with
principal-unit transitions, on a selected covering family of opens.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAActualNilpotentLineGluing318

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Ring

variable {B : Type*} [CommRing B]

private def expVal (e b : B) : B := 1 + e * b

private theorem expVal_mul (e : B) (he : e * e = 0) (a b : B) :
    expVal e a * expVal e b = expVal e (a + b) := by
  unfold expVal
  calc
    (1 + e * a) * (1 + e * b) = 1 + e * (a + b) + (e * e) * (a * b) := by ring
    _ = 1 + e * (a + b) := by rw [he, zero_mul, add_zero]

/-- The actual unit, with inverse one minus the same square-zero term. -/
@[expose] def nilUnit (e : B) (he : e * e = 0) (b : B) : Bˣ where
  val := expVal e b
  inv := expVal e (-b)
  val_inv := by rw [expVal_mul e he, add_neg_cancel] <;> simp [expVal]
  inv_val := by rw [expVal_mul e he, neg_add_cancel] <;> simp [expVal]

theorem nilUnit_val (e : B) (he : e * e = 0) (b : B) :
    (nilUnit e he b).val = 1 + e * b := by
  unfold nilUnit expVal
  rfl

theorem nilUnit_mul (e : B) (he : e * e = 0) (a b : B) :
    nilUnit e he a * nilUnit e he b = nilUnit e he (a+b) :=
  Units.ext (expVal_mul e he a b)

@[simp] theorem nilUnit_zero (e : B) (he : e * e = 0) :
    nilUnit e he 0 = 1 := by
  apply Units.ext
  rw [nilUnit_val, Units.val_one, mul_zero, add_zero]

theorem nilUnit_map {C : Type*} [CommRing C] (f : B →+* C)
    (e : B) (he : e * e = 0) (b : B) :
    Units.map f.toMonoidHom (nilUnit e he b) =
      nilUnit (f e) (by rw [← map_mul, he, map_zero]) (f b) := by
  apply Units.ext
  change f (nilUnit e he b).val = (nilUnit (f e) _ (f b)).val
  rw [nilUnit_val, nilUnit_val, map_add, map_mul, map_one]

/-- Specialization killing the global square-zero section makes the
actual transition unit one, regardless of the coefficient. -/
theorem nilUnit_map_of_kills {C : Type*} [CommRing C] (f : B →+* C)
    (e : B) (he : e * e = 0) (hf : f e = 0) (b : B) :
    Units.map f.toMonoidHom (nilUnit e he b) = 1 := by
  apply Units.ext
  change f (nilUnit e he b).val = 1
  rw [nilUnit_val, map_add, map_mul, map_one, hf, zero_mul, add_zero]

end Ring

variable {Y : Scheme.{u}} {ι : Type u}

/-- Use the true restriction in the original structure sheaf, not a
separate affine chart coefficient map. -/
@[expose] def restrict {V W : Y.Opens} (h : W ≤ V) : Γ(Y,V) →+* Γ(Y,W) :=
  (Y.presheaf.map (homOfLE h).op).hom

variable (U : ι → Y.Opens)

structure AdditiveCocycle where
  coeff : ∀ i j, Γ(Y,U i ⊓ U j)
  diagonal : ∀ i, coeff i i = 0
  triple : ∀ i j k,
    restrict inf_le_left (coeff i j) +
      restrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (coeff j k) =
      restrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (coeff i k)

variable (e : Γ(Y,⊤)) (he : e * e = 0)

/-- The same global nilpotent restricted to this actual open. -/
@[expose] def epsilonOn (V : Y.Opens) : Γ(Y,V) := restrict le_top e

include he in
theorem epsilonOn_sq (V : Y.Opens) : epsilonOn e V * epsilonOn e V = 0 := by
  unfold epsilonOn
  rw [← map_mul, he, map_zero]

theorem epsilonOn_restrict {V W : Y.Opens} (h : W ≤ V) :
    restrict h (epsilonOn e V) = epsilonOn e W := by
  change Y.presheaf.map (homOfLE h).op
      (Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op e) =
    Y.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op e
  simp only [← Y.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]

@[expose] def transitionOn (V : Y.Opens) (b : Γ(Y,V)) : Γ(Y,V)ˣ :=
  nilUnit (epsilonOn e V) (epsilonOn_sq e he V) b

theorem transitionOn_restrict {V W : Y.Opens} (h : W ≤ V) (b : Γ(Y,V)) :
    UnitTransitionCocycle318.restrict (StructureUnitsSheaf318.units Y).obj h
        (transitionOn e he V b) =
      transitionOn e he W (restrict h b) := by
  apply Units.ext
  change restrict h (transitionOn e he V b).val =
    (transitionOn e he W (restrict h b)).val
  unfold transitionOn
  rw [nilUnit_val, nilUnit_val, map_add, map_mul, map_one, epsilonOn_restrict]

/-- Diagonal and triple equations are proved for the full original
overlap units from the given exact additive differences. -/
@[expose] def unitCocycle (c : AdditiveCocycle U) :
    UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units Y).obj U where
  transition i j := transitionOn e he (U i ⊓ U j) (c.coeff i j)
  diagonal i := by
    rw [c.diagonal]
    exact nilUnit_zero _ _
  triple i j k := by
    rw [transitionOn_restrict, transitionOn_restrict, transitionOn_restrict]
    unfold transitionOn
    rw [nilUnit_mul, c.triple]

variable (c : AdditiveCocycle U)

/-- The actual line, with its real local frames over the selected opens.
Its underlying module is the stock compatible-coefficient equalizer;
no line-bundle object or gluing witness is assumed from the caller. -/
@[expose] def line (hc : (⊤ : Y.Opens) ≤ ⨆ i, U i) : LineSheafClass318.Line Y where
  object := CocycleModule318.object U (unitCocycle U e he c)
  Index := ι
  opens := U
  cover := hc
  frame := CocycleCanonicalTransitions318.frames U (unitCocycle U e he c)

theorem line_exact_transitions (hc : (⊤ : Y.Opens) ≤ ⨆ i, U i) :
    LineFrameCocycle318.cocycle (line U e he c hc).object U (line U e he c hc).frame =
      unitCocycle U e he c :=
  CocycleCanonicalTransitions318.cocycle_eq U (unitCocycle U e he c)

end SelectedSameAActualNilpotentLineGluing318
