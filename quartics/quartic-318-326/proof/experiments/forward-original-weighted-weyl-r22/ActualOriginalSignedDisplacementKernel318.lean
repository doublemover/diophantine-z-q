module
public import ActualOriginalCompleteFiveKernel318
public section
noncomputable section
namespace ActualOriginalSignedDisplacementKernel318
open ActualOriginalRationalBlockReciprocalSum318 ActualOriginalWeightedBlockReciprocalBudget318
open ActualOriginalCompleteTwoAxisWeyl318
open scoped BigOperators

@[expose] def signedEvenKernel (m H : ℤ) (N t : ℝ) : ℝ :=
  ∑ a∈Finset.Icc (-2*H) (2*H), fourierChordCap N (2*(m*a)) t
lemma actual_signed_even_nonneg (m H : ℤ) (N t : ℝ) (hN : 0≤N) :
    0≤signedEvenKernel m H N t :=
  Finset.sum_nonneg (fun a ha => actual_chord_cap_nonneg _ _ _ hN)
lemma actual_signed_even_one (H : ℤ) (N t : ℝ) :
    signedEvenKernel 1 H N t=completeEvenKernel H N t := by
  simp only [signedEvenKernel,completeEvenKernel,one_mul]

/-- Nonzero signed coefficient multiplication is injective. The enlarged
range uses its ABSOLUTE value; no unjustified q-coprimality is substituted.
This statement deliberately excludes m=0. -/
theorem actual_signed_even_range (m H : ℤ) (N t : ℝ) (hm : m≠0) (hH : 0≤H) (hN : 0≤N) :
    signedEvenKernel m H N t≤completeEvenKernel (|m|*H) N t := by
  let s := Finset.Icc (-2*H) (2*H)
  have hinj : Set.InjOn (fun a : ℤ => m*a) (s : Set ℤ) := by
    intro a ha b hb he
    exact mul_left_cancel₀ hm he
  have hsub : s.image (fun a => m*a)⊆Finset.Icc (-2*(|m|*H)) (2*(|m|*H)) := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hab := Finset.mem_Icc.mp ha
    have ha' : |a|≤2*H := abs_le.mpr ⟨by omega,hab.2⟩
    have hm' : |m*a|≤2*(|m|*H) := by
      rw [abs_mul]
      have hh := mul_le_mul_of_nonneg_left ha' (abs_nonneg m)
      nlinarith
    have hh := abs_le.mp hm'
    exact Finset.mem_Icc.mpr ⟨by linarith,hh.2⟩
  calc
    _ = ∑ a∈s.image (fun a => m*a), fourierChordCap N (2*a) t := by
      rw [Finset.sum_image (fun a ha b hb he => hinj ha hb he)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a ha hnot => actual_chord_cap_nonneg _ _ _ hN)

end ActualOriginalSignedDisplacementKernel318
