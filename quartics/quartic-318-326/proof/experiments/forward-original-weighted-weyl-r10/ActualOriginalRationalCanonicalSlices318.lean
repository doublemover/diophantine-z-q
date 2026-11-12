module
public import ActualOriginalRationalFrequencyCancellation318
public section
noncomputable section
namespace ActualOriginalRationalCanonicalSlices318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCompactCircleCount318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCanonicalOverlapLength318
open ActualOriginalCanonicalSliceCancellation318 ActualOriginalRationalFrequencyCancellation318
open ActualOriginalBoxOverlap318 ActualOriginalBoxSliceAggregation318
open ActualOriginalIntervalSliceIdentity318 ActualOriginalQuadraticPolarization318
open scoped ContDiff

lemma actual_first_bilinear_frequency (κ : ℤ) (h : Coordinates ℤ) :
    2*originalBilinear κ h firstDirection=2*h.1.1 := by
  simp [originalBilinear,firstDirection]

/-- One R,A,L works for every rational approximation and every actual
canonical slice in its controlled nonmultiple-frequency block. This
removes a per-slice assumed chord separation, not the global outer sum. -/
theorem actual_rational_canonical_slice_cancellation (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R A L : ℝ, 1≤R ∧ 0≤A ∧ 0≤L ∧
      (∀ B : ℝ, 0<B → ∀ z∉centeredBox ⌈R*B⌉, latticeWeight B W z=0) ∧
      ∀ B : ℝ, 1≤B → ∀ h : Coordinates ℤ, ∀ b c d e : ℤ,
      ∀ a q : ℤ, 0<q → IsCoprime q a → ¬q∣2*h.1.1 →
      ∀ t : ℝ, |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2 →
      |((2*h.1.1 : ℤ) : ℝ)|≤(q : ℝ)/2 →
      ‖sliceCorrelation κ (latticeWeight B W) (t : AddCircle (1 : ℝ)) h
        (overlap (Finset.Icc (-⌈R*B⌉) ⌈R*B⌉) h.1.1) b c d e‖≤
        min (overlapLength ⌈R*B⌉ h.1.1 : ℝ) (q : ℝ)*
          (A^2+2*A*(2*R+3)*L*‖integerEmbed firstDirection‖) := by
  obtain ⟨R,A,L,hR,hA,hL,hs,hl⟩ := actual_canonical_smooth_slice_cancellation κ W hW hc
  refine ⟨R,A,L,hR,hA,hL,hs,fun B hB h b c d e a q hq ha hnon t ht hsize => ?_⟩
  obtain ⟨hn,hbound⟩ := actual_rational_frequency_bound a q (2*h.1.1) t hq ha hnon ht hsize
  have hn' : fourier (2*originalBilinear κ h firstDirection) (t : AddCircle (1 : ℝ))≠1 := by
    simpa only [actual_first_bilinear_frequency] using hn
  have hb := hl B hB h b c d e (t : AddCircle (1 : ℝ)) hn'
  rw [actual_first_bilinear_frequency] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right (min_le_min le_rfl hbound)
  have hR' : 0≤2*R+3 := by linarith
  positivity

end ActualOriginalRationalCanonicalSlices318
