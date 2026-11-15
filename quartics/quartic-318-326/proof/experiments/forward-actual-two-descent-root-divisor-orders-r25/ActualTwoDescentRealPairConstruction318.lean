module
public import ActualTwoDescentAdelicNormalization318
public section
noncomputable section
namespace ActualTwoDescentRealPairConstruction318
set_option maxHeartbeats 16000000

open ActualTwoDescentTorsionSquarePairs318

lemma actual_real_pair_from_signs (n x A B : ℝ) (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0)
    (hc : 0 ≤ x*(x-n)*(x+3*n)) (hAr : 0 < (x+3*n)/A) (hBr : 0 < (x-n)/B)
    (hAz : A ≠ 0) (hBz : B ≠ 0) :
    ∃ y : ℝ, y^2=x*(x-n)*(x+3*n) ∧ SquarePair (x+3*n) (x-n) A B := by
  refine ⟨Real.sqrt (x*(x-n)*(x+3*n)),Real.sq_sqrt hc,
    Real.sqrt ((x+3*n)/A),Real.sqrt ((x-n)/B),
    (Real.sqrt_pos.mpr hAr).ne',(Real.sqrt_pos.mpr hBr).ne',?_,?_⟩
  · rw [Real.sq_sqrt hAr.le]; field_simp [hAz]
  · rw [Real.sq_sqrt hBr.le]; field_simp [hBz]

/-- Every positive first class and either nonzero second sign has an actual
nonexceptional real representative on the ORIGINAL positive twist. -/
theorem actual_real_pair_representative (n A B : ℝ) (hn : 0 < n) (hA : 0 < A) (hB : B ≠ 0) :
    ∃ x y : ℝ, x ≠ 0 ∧ x-n ≠ 0 ∧ x+3*n ≠ 0 ∧
      y^2=x*(x-n)*(x+3*n) ∧ SquarePair (x+3*n) (x-n) A B := by
  by_cases hpos : 0 < B
  · have hx : n+1 ≠ 0 := by positivity
    have hminus : n+1-n ≠ 0 := by simpa only [show n+1-n=1 by ring] using (one_ne_zero : (1 : ℝ) ≠ 0)
    have hplus : n+1+3*n ≠ 0 := by positivity
    obtain ⟨y,hc,H⟩ := actual_real_pair_from_signs n (n+1) A B hx hminus hplus
      (by have h : n+1-n=1 := by ring; rw [h]; positivity)
      (div_pos (by positivity) hA) (div_pos (by linarith) hpos) hA.ne' hB
    exact ⟨n+1,y,hx,hminus,hplus,hc,H⟩
  · have hneg : B < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hB
    have hx : -n ≠ 0 := neg_ne_zero.mpr hn.ne'
    have hminus : -n-n ≠ 0 := by linarith
    have hplus : -n+3*n ≠ 0 := by linarith
    obtain ⟨y,hc,H⟩ := actual_real_pair_from_signs n (-n) A B hx hminus hplus
      (by have he : (-n)*(-n-n)*(-n+3*n)=4*n^3 := by ring; rw [he]; positivity)
      (div_pos (by linarith) hA) (div_pos_of_neg_of_neg (by linarith) hneg) hA.ne' hB
    exact ⟨-n,y,hx,hminus,hplus,hc,H⟩

end ActualTwoDescentRealPairConstruction318
