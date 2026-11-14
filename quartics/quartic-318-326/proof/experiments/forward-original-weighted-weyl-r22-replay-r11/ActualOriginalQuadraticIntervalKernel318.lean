module
public import ActualOriginalIntervalDifferencing318
public section
noncomputable section
namespace ActualOriginalQuadraticIntervalKernel318
open ActualOriginalIntervalDifferencing318 ActualOriginalQuadraticFourthMoment318
open ActualOriginalFiniteFourierEnergy318 ActualOriginalQuadraticShiftCancellation318
open ActualOriginalBoxOverlap318 ActualOriginalSignedDisplacementKernel318
open ActualOriginalRationalBlockReciprocalSum318 ActualOriginalCompleteTwoAxisWeyl318
open scoped BigOperators ComplexConjugate

/-- Each actual overlap is a consecutive interval. Its length is at most
2H+1 even when empty; the resonant branch retains that full length. -/
lemma actual_overlap_quadratic_cap (H lo hi c h : ℤ) (hH : 0≤H)
    (hlo : -H≤lo) (hhi : hi≤H) (t : ℝ) :
    ‖∑ y∈overlap (Finset.Icc lo hi) h,
      fourier (c*(h+y)^2) (t : AddCircle (1 : ℝ))*
        conj (fourier (c*y^2) (t : AddCircle (1 : ℝ)))‖≤
      fourierChordCap (2*(H : ℝ)+1) (2*(c*h)) t := by
  let l := max lo (lo-h)
  let u := min hi (hi-h)
  let n := (u-l+1).toNat
  have hn : (n : ℤ)≤2*H+1 := by dsimp [n,u,l]; omega
  have hnR : (n : ℝ)≤2*(H : ℝ)+1 := by exact_mod_cast hn
  rw [actual_interval_overlap,actual_integer_interval_sum]
  have he : (∑ j∈Finset.range n,
      fourier (c*(h+(l+(j : ℤ)))^2) (t : AddCircle (1 : ℝ))*
        conj (fourier (c*(l+(j : ℤ))^2) (t : AddCircle (1 : ℝ))))=
      quadraticShiftCorrelation c h l n (t : AddCircle (1 : ℝ)) := by
    simp only [quadraticShiftCorrelation,add_comm h]
  change ‖∑ j∈Finset.range n, _‖≤_
  rw [he]
  have hfreq : 2*c*h=2*(c*h) := by ring
  by_cases hr : fourier (2*(c*h)) (t : AddCircle (1 : ℝ))=1
  · rw [fourierChordCap,if_pos hr]
    exact (actual_quadratic_shift_length_bound c h l n _).trans hnR
  · rw [fourierChordCap,if_neg hr]
    have hb := actual_quadratic_shift_cancellation c h l n (t : AddCircle (1 : ℝ))
      (by simpa only [hfreq] using hr)
    apply hb.trans
    simpa only [hfreq] using min_le_min hnR (le_refl (2/‖fourier (2*c*h) (t : AddCircle (1 : ℝ))-1‖))

/-- A uniform complete kernel bound for EVERY bounded consecutive
subinterval, not for arbitrary subsets. No prefix maximum is integrated. -/
theorem actual_quadratic_interval_kernel (H lo hi c : ℤ) (hH : 0≤H)
    (hlo : -H≤lo) (hhi : hi≤H) (hc : c≠0) (t : ℝ) :
    ‖quadraticSum (Finset.Icc lo hi) c (t : AddCircle (1 : ℝ))‖^2≤
      completeEvenKernel (|c|*H) (2*(H : ℝ)+1) t := by
  have hfirst := actual_interval_square_bound H lo hi hlo hhi
    (fun x => fourier (c*x^2) (t : AddCircle (1 : ℝ)))
  change ‖quadraticSum (Finset.Icc lo hi) c (t : AddCircle (1 : ℝ))‖^2≤_ at hfirst
  apply hfirst.trans
  calc
    _ ≤ signedEvenKernel c H (2*(H : ℝ)+1) t := by
      apply Finset.sum_le_sum
      intro h hh
      exact actual_overlap_quadratic_cap H lo hi c h hH hlo hhi t
    _ ≤ _ := actual_signed_even_range c H _ t hc hH
      (by have : (0 : ℝ)≤H := by exact_mod_cast hH; positivity)

end ActualOriginalQuadraticIntervalKernel318
