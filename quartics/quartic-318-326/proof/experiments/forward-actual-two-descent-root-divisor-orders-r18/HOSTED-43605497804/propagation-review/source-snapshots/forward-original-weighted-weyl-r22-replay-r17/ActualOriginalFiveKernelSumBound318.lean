module
public import ActualOriginalSignedDisplacementKernel318
public section
noncomputable section
namespace ActualOriginalFiveKernelSumBound318
open QuadricCRTAssembly318 ActualOriginalWeightedWeylIdentity318
open ActualOriginalCanonicalSupportBox318 ActualOriginalFiveKernelCorrelation318
open ActualOriginalCompleteFiveKernel318 ActualOriginalSignedDisplacementKernel318
open ActualOriginalCompleteTwoAxisWeyl318 ActualOriginalRationalBlockReciprocalSum318
open ActualOriginalWeightedBlockReciprocalBudget318
open scoped BigOperators

@[expose] def completeFiveKernel (κ H : ℤ) (N t : ℝ) : ℝ :=
  signedEvenKernel 1 H N t*signedEvenKernel 1 H N t*
    signedEvenKernel (-1) H N t*signedEvenKernel (-1) H N t*signedEvenKernel (-κ) H N t

lemma actual_five_kernel_sum (κ H : ℤ) (N t : ℝ) (hN : 0≤N) :
    (∑ h∈differences (centeredBox H), fiveChordProduct κ N t h)≤completeFiveKernel κ H N t := by
  have hh := actual_complete_five_kernel H
    (fun a => fourierChordCap N (2*a) t) (fun a => fourierChordCap N (2*a) t)
    (fun a => fourierChordCap N (2*(-a)) t) (fun a => fourierChordCap N (2*(-a)) t)
    (fun a => fourierChordCap N (2*(-(κ*a))) t)
    (fun a => actual_chord_cap_nonneg _ _ _ hN) (fun a => actual_chord_cap_nonneg _ _ _ hN)
    (fun a => actual_chord_cap_nonneg _ _ _ hN) (fun a => actual_chord_cap_nonneg _ _ _ hN)
    (fun a => actual_chord_cap_nonneg _ _ _ hN)
  simpa only [fiveChordProduct,completeFiveKernel,signedEvenKernel,one_mul,neg_one_mul,neg_mul] using hh

/-- The four unit coefficients and the nonzero original kappa coefficient
all retain complete kernel sums. No coprimality of kappa with q is needed:
the last signed multiplication injects into its larger literal interval. -/
theorem actual_five_kernel_nonzero_coefficient (κ H : ℤ) (N t : ℝ)
    (hκ : κ≠0) (hH : 0≤H) (hN : 0≤N) :
    completeFiveKernel κ H N t≤
      (completeEvenKernel H N t)^4*completeEvenKernel (|κ|*H) N t := by
  have hneg : signedEvenKernel (-1) H N t≤completeEvenKernel H N t := by
    simpa only [abs_neg,abs_one,one_mul] using actual_signed_even_range (-1) H N t (by norm_num) hH hN
  have hk : signedEvenKernel (-κ) H N t≤completeEvenKernel (|κ|*H) N t := by
    simpa only [abs_neg] using actual_signed_even_range (-κ) H N t (neg_ne_zero.mpr hκ) hH hN
  have hS := actual_complete_even_kernel_nonneg H N t hN
  have hneg0 := actual_signed_even_nonneg (-1) H N t hN
  have hk0 := actual_signed_even_nonneg (-κ) H N t hN
  have hfour : (completeEvenKernel H N t)^2*(signedEvenKernel (-1) H N t)^2≤
      (completeEvenKernel H N t)^4 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hneg0 hneg 2) (sq_nonneg (completeEvenKernel H N t))
    convert hh using 1 <;> ring
  calc
    _ = ((completeEvenKernel H N t)^2*(signedEvenKernel (-1) H N t)^2)*
        signedEvenKernel (-κ) H N t := by
      simp only [completeFiveKernel,actual_signed_even_one]
      ring
    _ ≤ _ := mul_le_mul hfour hk hk0 (pow_nonneg hS 4)

end ActualOriginalFiveKernelSumBound318
