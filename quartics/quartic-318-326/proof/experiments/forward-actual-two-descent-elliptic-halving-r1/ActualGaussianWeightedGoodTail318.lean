module
public import ActualGaussianGoodSlice318
public section
noncomputable section
namespace ActualGaussianWeightedGoodTail318
open scoped BigOperators
open ActualGaussianGoodSlice318 ActualQuarticGoodFamily318 ActualQuarticSignedGoodTail318
open ActualQuarticLabelHeight318 OriginalGlobalBadMass318 OriginalUniformEulerRankin318
open OriginalBadSliceLogWeight318 OriginalWeightedSelberg318
set_option maxHeartbeats 10000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def mass (B : ℕ) (κ t : ℤ) (T : ℝ) (Y : ℕ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (GoodSlice B κ t T Y) := Fintype.ofFinite _
  exact ∑ v : GoodSlice B κ t T Y, weight κ γ v.1.1.1

lemma mass_le_card (B : ℕ) (hB : 1≤B) (κ t : ℤ) (T : ℝ) (Y : ℕ) (γ : J → ℤ) :
    mass B κ t T Y γ≤(Nat.card (GoodSlice B κ t T Y):ℝ)*weightCeiling B γ := by
  classical
  letI : Fintype (GoodSlice B κ t T Y) := Fintype.ofFinite _
  calc
    _ ≤ ∑ _v : GoodSlice B κ t T Y, weightCeiling B γ :=
      Finset.sum_le_sum (fun v _ => original_weight_bound B hB κ t true γ v.1)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]

@[expose] def totalMass (B : ℕ) (κ : ℤ) (T : ℝ) (Y : ℕ) (γ : J → ℤ) : ℝ :=
  ∑ t∈labels B, mass B κ t T Y γ

/-- The literal original logarithmic weights and all signed source labels
are now consumed, not supplied as a bound. This is the actual SECOND-chart
good-lattice contribution; zero labels, bad lattices, primes dividing the
label, and the other chart remain separate parts of the final sieve. -/
theorem actual_original_weighted_good_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (T : ℝ) (hT : 0≤T) (hTB : T≤6*(B:ℝ)) (Y : ℕ) (hY : 3≤Y)
    (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    totalMass B κ T Y γ*Real.log (Y:ℝ)≤
      (2*rankinConstant κ δ*(2*(B:ℝ))^δ)*
        labelBudget κ B (6*(B:ℝ)) T Y*weightCeiling B γ := by
  have hW := weightCeiling_nonneg B hB γ
  have hlog := Real.log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hfixed (t : ℤ) (ht : t∈labels B) :
      mass B κ t T Y γ≤
        (Nat.card (GoodPoints (2*B) κ t (6*(B:ℝ)) T Y):ℝ)*weightCeiling B γ := by
    have hc : (Nat.card (GoodSlice B κ t T Y):ℝ)≤
        (Nat.card (GoodPoints (2*B) κ t (6*(B:ℝ)) T Y):ℝ) := by
      exact_mod_cast actual_source_card B κ t (label_ne_zero B t ht) T Y hY
    exact (mass_le_card B hB κ t T Y γ).trans (mul_le_mul_of_nonneg_right hc hW)
  have hs := Finset.sum_le_sum hfixed
  have hm : totalMass B κ T Y γ≤signedCount (2*B) B κ (6*(B:ℝ)) T Y*weightCeiling B γ := by
    simpa only [totalMass,signedCount,Finset.sum_mul] using hs
  have hc := actual_signed_good_tail (2*B) B κ hκ (6*(B:ℝ)) T
    (by positivity) hT hTB Y hY δ hδ
  calc
    _ ≤ (signedCount (2*B) B κ (6*(B:ℝ)) T Y*weightCeiling B γ)*Real.log (Y:ℝ) :=
      mul_le_mul_of_nonneg_right hm hlog
    _ = (signedCount (2*B) B κ (6*(B:ℝ)) T Y*Real.log (Y:ℝ))*weightCeiling B γ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hW

end ActualGaussianWeightedGoodTail318
