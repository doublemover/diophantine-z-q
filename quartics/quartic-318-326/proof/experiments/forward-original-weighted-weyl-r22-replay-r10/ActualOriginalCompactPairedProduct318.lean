module
public import ActualOriginalSmoothAllDifferenceOrders318
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
public section
noncomputable section
namespace ActualOriginalCompactPairedProduct318
open QuadricCRTAssembly318 ActualOriginalUniformPairedMixedConstants318
open ActualOriginalIteratedDifference318 ActualOriginalSmoothAllDifferenceOrders318
open scoped ContDiff

@[expose] def pairedProduct (W : Coordinates ℝ → ℝ)
    (p : Coordinates ℝ × Coordinates ℝ) : ℝ := W p.1*W p.2
@[expose] def diagonalStep (u : Coordinates ℝ) : Coordinates ℝ × Coordinates ℝ := (u,u)

lemma actual_paired_product_smooth (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (pairedProduct W) :=
  (hW.comp contDiff_fst).mul (hW.comp contDiff_snd)

/-- The product on the doubled ORIGINAL space has compact support in
the product of the two actual supports. Neither projection alone is
incorrectly asserted compactly supported. -/
lemma actual_paired_product_compact (W : Coordinates ℝ → ℝ) (hc : HasCompactSupport W) :
    HasCompactSupport (pairedProduct W) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.isCompact.prod hc.isCompact)
  intro p hp
  have hn : W p.1*W p.2≠0 := hp
  exact ⟨subset_tsupport W (mul_ne_zero_iff.mp hn).1,
    subset_tsupport W (mul_ne_zero_iff.mp hn).2⟩

lemma actual_paired_mixed_diagonal (W : Coordinates ℝ → ℝ) (h : Coordinates ℝ)
    (us : List (Coordinates ℝ)) : ∀ x,
    mixedDifference (translatedPairedWeight W h) us x=
      mixedDifference (pairedProduct W) (us.map diagonalStep) (x+h,x) := by
  induction us with
  | nil => intro x; rfl
  | cons u us ih =>
    intro x
    have he : (x+u+h,x+u)=(x+h,x)+diagonalStep u := by
      apply Prod.ext
      · dsimp [diagonalStep]; abel
      · rfl
    simpa only [List.map_cons,mixedDifference,ih,he]

lemma actual_diagonal_direction_product (us : List (Coordinates ℝ)) :
    directionProduct (us.map diagonalStep)=directionProduct us := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [List.map_cons,directionProduct,diagonalStep,Prod.norm_def,max_self,ih]

/-- ALL mixed orders of BOTH paired factors have produced constants
uniform over every translation. Diagonal steps have exactly the original
norm; no h-dependent support or derivative constant is selected. -/
theorem actual_uniform_paired_all_orders (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (k : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ h : Coordinates ℝ, ∀ us : List (Coordinates ℝ),
      us.length=k → ∀ x, ‖mixedDifference (translatedPairedWeight W h) us x‖≤C*directionProduct us := by
  obtain ⟨C,hC,hb⟩ := actual_smooth_all_difference_orders (Coordinates ℝ × Coordinates ℝ) k
    ℝ (pairedProduct W) (actual_paired_product_smooth W hW) (actual_paired_product_compact W hc)
  refine ⟨C,hC,fun h us hu x => ?_⟩
  rw [actual_paired_mixed_diagonal]
  have hh := hb (us.map diagonalStep) (by simpa only [List.length_map] using hu) (x+h,x)
  simpa only [actual_diagonal_direction_product] using hh

end ActualOriginalCompactPairedProduct318
