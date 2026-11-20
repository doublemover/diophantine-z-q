module
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace SelectedJOneLocalDegree318
open NumberField Function

variable {L : Type*} [Field L] [NumberField L]

/-- The actual normalized finite places of the evaluation field, not of
the field controlling the isogeny. Local frames may all differ. -/
def finiteColumn (u : FinitePlace L → L) : ℝ :=
  -(∑ᶠ v : FinitePlace L, Real.log (v (u v))) / (Module.finrank ℚ L:ℝ)

/-- Passing from the resolution coefficient ds to the coefficient dm
on the minimal semistable model preserves the integral dual witness.
The one coefficient c is the restriction of the actual relative
dualizing sheaf comparison, not an arbitrary change of rational basis. -/
theorem compare_frames (v : FinitePlace L) {b ds dm c t : L}
    (coefficient : ds=c*dm) (hc : v c ≤ 1) (ht : v t ≤ 1) (eval : ds*t=b) :
    ∃ t' : L, v t' ≤ 1 ∧ dm*t'=b := by
  refine ⟨c*t, ?_, ?_⟩
  · rw [map_mul]
    exact (mul_le_of_le_one_right (apply_nonneg v c) ht).trans hc
  · calc
      dm*(c*t) = (c*dm)*t := by ring
      _ = b := by rw [←coefficient,eval]

/-- Pulling back the dualizing inverse section at j=1 gives a witness
t with ord_v(t)≥0 and u_v t = -1727M. Multiplying its pole-free coefficient
by the unit -1 permits the positive integer b=1727M below. This proof
takes the genuine finite norms and pays each prime exactly once after
division by [L:Q]. It needs no intersection matrix or split section places. -/
theorem from_integral_ratio (u : FinitePlace L → L) (b : ℕ) (hb : 0 < b)
    (hu : HasFiniteMulSupport (fun v : FinitePlace L => v (u v)))
    (up : ∀ v : FinitePlace L, 0 < v (u v))
    (witness : ∀ v : FinitePlace L, ∃ t : L, v t ≤ 1 ∧ u v*t=(b:L)) :
    finiteColumn u ≤ Real.log (b:ℝ) := by
  have hbL : (b:L) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hd : (0:ℝ) < Module.finrank ℚ L := by
    exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=L))
  have local_le (v : FinitePlace L) : v (b:L) ≤ v (u v) := by
    obtain ⟨t,hv,ht⟩ := witness v
    rw [←ht,map_mul]
    exact mul_le_of_le_one_right (apply_nonneg v _) hv
  have hp := finprod_le_finprod₀ (FinitePlace.hasFiniteMulSupport hbL)
    (fun v => apply_nonneg v (b:L)) hu local_le
  have hnorm : (∏ᶠ v : FinitePlace L,v (b:L)) =
      ((b:ℝ)^Module.finrank ℚ L)⁻¹ := by
    rw [FinitePlace.prod_eq_inv_abs_norm hbL,Algebra.norm_natCast,
      abs_of_nonneg (show 0 ≤ (b:ℚ)^Module.finrank ℚ L by positivity)]
    push_cast <;> rfl
  have hpos : 0 < (∏ᶠ v : FinitePlace L,v (b:L)) := by
    rw [hnorm]
    positivity
  have hlog := Real.log_le_log hpos hp
  rw [hnorm,Real.log_inv,Real.log_pow,Real.log_finprod up] at hlog
  unfold finiteColumn
  calc
    _ ≤ ((Module.finrank ℚ L:ℝ)*Real.log (b:ℝ))/(Module.finrank ℚ L:ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hd.le
    _ = Real.log (b:ℝ) := (div_eq_iff hd.ne').mpr (mul_comm _ _)

/-- The exact numerical ceiling for the ordinary j=1 differential
row. The only remaining inputs here are the actual comparisons at
each place, and that a line-bundle frame has unit coefficient almost
everywhere. -/
theorem literal_bound (u : FinitePlace L → L) (M : ℕ) (hM : 0 < M)
    (hu : HasFiniteMulSupport (fun v : FinitePlace L => v (u v)))
    (up : ∀ v : FinitePlace L, 0 < v (u v))
    (witness : ∀ v : FinitePlace L, ∃ t : L, v t ≤ 1 ∧ u v*t=((1727*M:ℕ):L)) :
    finiteColumn u ≤ Real.log (M:ℝ)+Real.log 1727 := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hh := from_integral_ratio u (1727*M) (by positivity) hu up witness
  have hC : ((1727 : ℕ) : ℝ) ≠ 0 := by positivity
  calc
    finiteColumn u ≤ Real.log ((1727 * M : ℕ) : ℝ) := hh
    _ = Real.log (((1727 : ℕ) : ℝ) * (M : ℝ)) := congrArg Real.log (Nat.cast_mul 1727 M)
    _ = Real.log ((1727 : ℕ) : ℝ) + Real.log (M : ℝ) := Real.log_mul hC hM'.ne'
    _ = Real.log (M : ℝ) + Real.log 1727 := by
      simpa only [Nat.cast_ofNat] using (add_comm (Real.log ((1727 : ℕ) : ℝ)) (Real.log (M : ℝ)))

end SelectedJOneLocalDegree318
#print axioms SelectedJOneLocalDegree318.literal_bound
