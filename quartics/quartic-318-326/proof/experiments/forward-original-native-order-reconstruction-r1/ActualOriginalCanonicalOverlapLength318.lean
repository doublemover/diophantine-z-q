module
public import ActualOriginalCanonicalSupportBox318
public section
noncomputable section
namespace ActualOriginalCanonicalOverlapLength318
open ActualOriginalBoxOverlap318
open scoped BigOperators

@[expose] def overlapLength (H h : ℤ) : ℕ :=
  (min H (H-h)-max (-H) (-H-h)+1).toNat

/-- All actual overlap intervals of a centered original box have this
uniform length bound, including empty overlaps and large displacements. -/
lemma actual_overlap_length_le (H h : ℤ) (hH : 0≤H) :
    (overlapLength H h : ℤ)≤2*H+1 := by
  have hu : min H (H-h)≤H := min_le_left _ _
  have hl : -H≤max (-H) (-H-h) := le_max_left _ _
  unfold overlapLength
  omega

lemma actual_scaled_radius_nonneg (R B : ℝ) (hR : 0≤R) (hB : 0≤B) :
    0≤⌈R*B⌉ := by
  have hh : (0 : ℝ)≤(⌈R*B⌉ : ℝ) := (mul_nonneg hR hB).trans (Int.le_ceil (R*B))
  exact_mod_cast hh

/-- A single linear-in-scale budget controls EVERY coordinate overlap
length. The additive ceiling loss is absorbed only under the explicit B>=1. -/
theorem actual_canonical_overlap_scale_bound (R B : ℝ) (hR : 0≤R) (hB : 1≤B)
    (h : ℤ) : (overlapLength ⌈R*B⌉ h : ℝ)≤(2*R+3)*B := by
  have hi := actual_overlap_length_le ⌈R*B⌉ h (actual_scaled_radius_nonneg R B hR (by linarith))
  have hi' : (overlapLength ⌈R*B⌉ h : ℝ)≤2*(⌈R*B⌉ : ℝ)+1 := by exact_mod_cast hi
  have hh := Int.ceil_lt_add_one (R*B)
  nlinarith

/-- The natural reindexing in the original slice theorem uses exactly
this constructed length, not a subsequently selected number of terms. -/
lemma actual_canonical_overlap_sum (f : ℤ → ℂ) (H h : ℤ) :
    (∑ a ∈ overlap (Finset.Icc (-H) H) h, f a)=
      ∑ j ∈ Finset.range (overlapLength H h), f (max (-H) (-H-h)+(j : ℤ)) := by
  rw [actual_interval_overlap,actual_integer_interval_sum]
  rfl

end ActualOriginalCanonicalOverlapLength318
