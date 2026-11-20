module
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public section
noncomputable section
open NumberField
open scoped BigOperators

namespace SelectedJOneExactMinorLoss318

variable {L : Type*} [Field L] [NumberField L]

/-- The norm-≤1 subring for the genuine normalized finite place of L.
No further weight for the residue degree is attached to this norm. -/
def integralAt (v : FinitePlace L) : Subring L where
  carrier := {x | v x ≤ 1}
  zero_mem' := by change v 0 ≤ 1; rw [map_zero]; norm_num
  one_mem' := by change v 1 ≤ 1; rw [map_one]
  add_mem' := by
    intro x y hx hy
    exact (v.add_le x y).trans (max_le hx hy)
  mul_mem' := by
    intro x y hx hy
    change v (x*y) ≤ 1
    rw [map_mul]
    exact (mul_le_of_le_one_right (apply_nonneg v x) hy).trans hx
  neg_mem' := by
    intro x hx
    change v (-x) ≤ 1
    rw [map_neg_eq_map]
    simpa only [Set.mem_setOf_eq] using hx

abbrev baseMatrix (v : FinitePlace L) {g : ℕ}
    (I : Matrix (Fin g) (Fin g) (integralAt v)) : Matrix (Fin g) (Fin g) L :=
  (integralAt v).subtype.mapMatrix I

theorem det_integral (v : FinitePlace L) {g : ℕ}
    (I : Matrix (Fin g) (Fin g) (integralAt v)) :
    v (baseMatrix v I).det ≤ 1 := by
  change v (((integralAt v).subtype.mapMatrix I).det) ≤ 1
  rw [← RingHom.map_det]
  exact I.det.property

/-- Exact finite contribution, not just an inequality: the SAME
evaluation minor m, same basis change C and actual integral matrix I.
The local logarithmic determinant loss is nonnegative. Identification
with a cokernel length times log Norm(p) is a separate DVR theorem;
this equation does not assert or assume that identification. -/
theorem exact_row (v : FinitePlace L) {g : ℕ}
    (m C : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0) (hC : C.det ≠ 0)
    (u : Fin g → L) (hu : ∀ i, u i ≠ 0)
    (I : Matrix (Fin g) (Fin g) (integralAt v))
    (frames : baseMatrix v I = Matrix.diagonal u * m * C) :
    0 ≤ -Real.log (v (baseMatrix v I).det) ∧
    -Real.log (v ((m.det*C.det)⁻¹)) =
      (∑ i, -Real.log (v (u i))) - (-Real.log (v (baseMatrix v I).det)) := by
  let d := (baseMatrix v I).det
  let a := m.det*C.det
  have ha : a ≠ 0 := mul_ne_zero hm hC
  have huP : (∏ i,u i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hu i
  have hd : d = (∏ i,u i)*a := by
    dsimp only [d, a]
    rw [frames, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    ring
  have hd0 : d ≠ 0 := by rw [hd]; exact mul_ne_zero huP ha
  have hdpos : 0 < v d := v.1.pos_iff.mpr hd0
  have hapos : 0 < v a := v.1.pos_iff.mpr ha
  have hupos (i : Fin g) : 0 < v (u i) := v.1.pos_iff.mpr (hu i)
  have hlogd : Real.log (v d) = (∑ i, Real.log (v (u i))) + Real.log (v a) := by
    rw [hd, map_mul, map_prod,
      Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => (hupos i).ne')) hapos.ne',
      Real.log_prod (fun i _ => (hupos i).ne')]
  change 0 ≤ -Real.log (v d) ∧
    -Real.log (v a⁻¹) = (∑ i, -Real.log (v (u i))) - (-Real.log (v d))
  refine ⟨neg_nonneg.mpr (Real.log_nonpos hdpos.le (det_integral v I)), ?_⟩
  rw [map_inv₀, Real.log_inv, neg_neg, Finset.sum_neg_distrib]
  linarith only [hlogd]

/-- Normalized degree contribution, summed over genuine finite places. -/
def degree (q : FinitePlace L → L) : ℝ :=
  (∑ᶠ v : FinitePlace L, -Real.log (v (q v))) / (Module.finrank ℚ L : ℝ)

theorem degree_eq_finset (V : Finset (FinitePlace L)) (q : FinitePlace L → L)
    (off : ∀ v ∉ V, v (q v) = 1) :
    degree q = (∑ v ∈ V, -Real.log (v (q v))) / (Module.finrank ℚ L : ℝ) := by
  classical
  have hs : Function.support (fun v : FinitePlace L => -Real.log (v (q v))) ⊆
      (V : Set (FinitePlace L)) := by
    intro v hv
    change v ∈ V
    by_contra hnot
    apply hv
    change -Real.log (v (q v)) = 0
    rw [off v hnot, Real.log_one, neg_zero]
  unfold degree
  rw [finsum_eq_finsetSum_of_support_subset _ hs]

/-- Global assembly with a finite set carrying all nonunit norms (line
frames are units almost everywhere). The individual degrees still sum
over all actual finite places, and are divided by [L:Q] exactly once.
The evaluation field L never needs an isogeny-degree bound. -/
theorem exact_finite {g : ℕ} (m : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0)
    (C : FinitePlace L → Matrix (Fin g) (Fin g) L) (hC : ∀ v, (C v).det ≠ 0)
    (u : FinitePlace L → Fin g → L) (hu : ∀ v i, u v i ≠ 0)
    (I : (v : FinitePlace L) → Matrix (Fin g) (Fin g) (integralAt v))
    (frames : ∀ v, baseMatrix v (I v) = Matrix.diagonal (u v) * m * C v)
    (V : Finset (FinitePlace L))
    (off : ∀ v ∉ V, (∀ i, v (u v i) = 1) ∧ v (baseMatrix v (I v)).det = 1 ∧
      v ((m.det*(C v).det)⁻¹) = 1) :
    let loss := degree (fun v => (baseMatrix v (I v)).det)
    0 ≤ loss ∧ degree (fun v => (m.det*(C v).det)⁻¹) =
      (∑ i, degree (fun v => u v i)) - loss := by
  dsimp only
  have h (v : FinitePlace L) := exact_row v m (C v) hm (hC v) (u v) (hu v) (I v) (frames v)
  have hl := degree_eq_finset V (fun v => (baseMatrix v (I v)).det) (fun v hv => (off v hv).2.1)
  have ha := degree_eq_finset V (fun v => (m.det*(C v).det)⁻¹) (fun v hv => (off v hv).2.2)
  have hu' (i : Fin g) := degree_eq_finset V (fun v => u v i) (fun v hv => (off v hv).1 i)
  rw [hl, ha]
  refine ⟨div_nonneg (Finset.sum_nonneg (fun v _ => (h v).1))
      (Nat.cast_nonneg _), ?_⟩
  simp_rw [hu']
  rw [← Finset.sum_div, ← sub_div]
  apply congrArg (fun x : ℝ => x / (Module.finrank ℚ L : ℝ))
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun v _ => (h v).2)

end SelectedJOneExactMinorLoss318
#print axioms SelectedJOneExactMinorLoss318.exact_row
#print axioms SelectedJOneExactMinorLoss318.exact_finite
