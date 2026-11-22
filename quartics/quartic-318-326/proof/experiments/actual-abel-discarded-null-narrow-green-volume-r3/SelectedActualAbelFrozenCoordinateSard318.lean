module

public import SelectedActualAbelPointwiseDerivative318
public import SelectedActualAbelExceptionalSetNull318
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section
noncomputable section

open Filter MeasureTheory Set
open SelectedActualAbelPointwiseDerivative318
open scoped Topology

namespace SelectedActualAbelFrozenCoordinateSard318

variable {g : ℕ} {P : Type*}

abbrev V := OrderedPeriodCoordinates g

/-- Full ambient-dimensional presentation: the ordinary coordinates
move independently and each selected discarded point retains its
actual constant Abel lift, with no chart around that point needed. -/
def maskedTerm (s : Fin g → Option P) (c : P → V (g := g))
    (l : Fin g → ℂ → ℂ) (i j : Fin g) (z : ℂ) : ℂ :=
  (s j).elim (l i z) (fun a => c a i)

def maskedSum (s : Fin g → Option P) (c : P → V (g := g))
    (l : Fin g → ℂ → ℂ) (x : V (g := g)) : V (g := g) :=
  fun i => ∑ j : Fin g, maskedTerm s c l i j (x j)

def maskedMatrix (s : Fin g → Option P) (d : Fin g → ℂ → ℂ) (x : V (g := g)) :
    Matrix (Fin g) (Fin g) ℂ :=
  fun i j => (s j).elim (d i (x j)) (fun _ => 0)

/-- As soon as at least one slot is a genuinely fixed point,
the full-size derivative has an actual zero column. The exact same
ambient-dimensional Sard lemma applies, with no codimension or
manifold-measure implementation and no differentiability at the
discarded points themselves. -/
theorem masked_sum_image_null
    (s : Fin g → Option P) (j₀ : Fin g) (p₀ : P) (hs : s j₀ = some p₀)
    (c : P → V (g := g)) (l d : Fin g → ℂ → ℂ)
    (W : Set ℂ) (hd : ∀ i : Fin g, ∀ z ∈ W, HasDerivAt (l i) (d i z) z) :
    (volume : Measure (V (g := g))) (maskedSum s c l '' (Set.univ.pi fun _ => W)) = 0 := by
  let S : Set (V (g := g)) := Set.univ.pi fun _ => W
  have hD (x : V (g := g)) (hx : x ∈ S) :
      HasFDerivAt (maskedSum s c l) (abelLinear (maskedMatrix s d x)) x := by
    have hsD (i j : Fin g) :
        HasDerivAt (maskedTerm s c l i j) (maskedMatrix s d x i j) (x j) := by
      have hW : x j ∈ W := hx j (Set.mem_univ j)
      cases h : s j with
      | none =>
        have hfun : maskedTerm s c l i j = l i := by
          funext z
          simp only [maskedTerm,h,Option.elim_none]
        have hval : maskedMatrix s d x i j = d i (x j) := by
          simp only [maskedMatrix,h,Option.elim_none]
        rw [hfun,hval]
        exact hd i (x j) hW
      | some a =>
        have hfun : maskedTerm s c l i j = (fun _ : ℂ => c a i) := by
          funext z
          simp only [maskedTerm,h,Option.elim_some]
        have hval : maskedMatrix s d x i j = 0 := by
          simp only [maskedMatrix,h,Option.elim_some]
        rw [hfun,hval]
        exact hasDerivAt_const (x j) (c a i)
    apply hasFDerivAt_abelSum_of_degreeOne x (maskedTerm s c l)
      (0 : V (g := g)) (maskedMatrix s d x) hsD (maskedSum s c l)
    exact Filter.Eventually.of_forall fun y => by
      funext i
      change (∑ j : Fin g, maskedTerm s c l i j (y j)) =
        (0 : ℂ) + ∑ j : Fin g, maskedTerm s c l i j (y j)
      exact (zero_add _).symm
  apply SelectedActualAbelExceptionalSetNull318.critical_image_null
    volume (maskedSum s c l) (fun x => abelLinear (maskedMatrix s d x)) S
  · exact fun x hx => (hD x hx).hasFDerivWithinAt
  · intro x _
    rw [abelLinear_det]
    apply Matrix.det_eq_zero_of_column_eq_zero j₀
    intro i
    simp only [maskedMatrix,hs,Option.elim_some]

end SelectedActualAbelFrozenCoordinateSard318

#print axioms SelectedActualAbelFrozenCoordinateSard318.masked_sum_image_null
