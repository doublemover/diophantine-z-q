module
public import ActualOriginalCanonicalMinorBudget318
public section
noncomputable section
namespace ActualOriginalCanonicalSliceCancellation318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCompactCircleCount318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCanonicalOverlapLength318
open ActualOriginalUniformLineCancellation318 ActualOriginalIntervalSliceIdentity318
open ActualOriginalBoxOverlap318 ActualOriginalBoxSliceAggregation318
open ActualOriginalLineCorrelation318 ActualOriginalQuadraticPolarization318
open scoped ContDiff

/-- Constants and a canonical support box are produced BEFORE every scale,
frequency, displacement and all four outer coordinates. The same exact
first-coordinate overlap slices used by canonicalSliceBudget receive the
scale-uniform nonresonant bound. This does not estimate their outer sum. -/
theorem actual_canonical_smooth_slice_cancellation (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R A L : ℝ, 1≤R ∧ 0≤A ∧ 0≤L ∧
      (∀ B : ℝ, 0<B → ∀ z∉centeredBox ⌈R*B⌉, latticeWeight B W z=0) ∧
      ∀ B : ℝ, 1≤B → ∀ h : Coordinates ℤ, ∀ b c d e : ℤ,
      ∀ θ : AddCircle (1 : ℝ), fourier (2*originalBilinear κ h firstDirection) θ≠1 →
      ‖sliceCorrelation κ (latticeWeight B W) θ h
        (overlap (Finset.Icc (-⌈R*B⌉) ⌈R*B⌉) h.1.1) b c d e‖≤
        min (overlapLength ⌈R*B⌉ h.1.1 : ℝ)
          (2/‖fourier (2*originalBilinear κ h firstDirection) θ-1‖)*
          (A^2+2*A*(2*R+3)*L*‖integerEmbed firstDirection‖) := by
  obtain ⟨R,hR,hs⟩ := actual_compact_canonical_support W hc
  obtain ⟨A,L,hA,hL,hl⟩ := actual_smooth_uniform_line_cancellation κ W hW hc
  refine ⟨R,A,L,hR,hA,hL,hs,fun B hB h b c d e θ hn => ?_⟩
  have hlen := actual_canonical_overlap_scale_bound R B (by linarith) hB h.1.1
  rw [actual_interval_overlap,actual_interval_slice_norm]
  change ‖originalLineCorrelation κ (latticeWeight B W) h
    ((max (-⌈R*B⌉) (-⌈R*B⌉-h.1.1),b),(c,d),e) firstDirection
      (overlapLength ⌈R*B⌉ h.1.1) θ‖≤_
  generalize heq : overlapLength ⌈R*B⌉ h.1.1=n at hlen ⊢
  cases n with
  | zero =>
      simp only [originalLineCorrelation,Finset.range_zero,Finset.sum_empty,norm_zero]
      have hR' : 0≤2*R+3 := by linarith
      positivity
  | succ n =>
      have hN : (n : ℝ)≤(2*R+3)*B := by
        rw [Nat.cast_succ] at hlen
        linarith
      simpa only [Nat.cast_succ] using hl B (by linarith) (2*R+3) h
        ((max (-⌈R*B⌉) (-⌈R*B⌉-h.1.1),b),(c,d),e) firstDirection n hN θ hn

end ActualOriginalCanonicalSliceCancellation318
