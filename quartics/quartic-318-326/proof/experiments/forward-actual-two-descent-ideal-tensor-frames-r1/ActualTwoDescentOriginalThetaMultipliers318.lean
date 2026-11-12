module
public import ActualTwoDescentOriginalRootAddition318
public section
noncomputable section
namespace ActualTwoDescentOriginalThetaMultipliers318
open ActualTwoDescentOriginalRootIdeals318 ActualTwoDescentOriginalRootTranslations318
variable {K : Type*} [Field K] [CharZero K]

/-- Multiplier in the composition of two weighted pullbacks, using
literal functions x-a and the actual root translations. -/
def thetaMultiplier (n x : K) (i j : Fin 3) : K :=
  rootWeight n x i*rootWeight n (rootTranslateX n x i) j

def thetaCommutator (n x : K) (i j : Fin 3) : K :=
  thetaMultiplier n x i j/thetaMultiplier n x j i

lemma actual_theta_multiplier_nonzero (n x : K) (hn : n ≠ 0)
    (hx : AwayRoots n x) (i j : Fin 3) : thetaMultiplier n x i j ≠ 0 :=
  mul_ne_zero (hx i) (actual_translation_away_roots n x hn hx i j)

lemma actual_theta_multiplier_skew (n x : K) (hx : AwayRoots n x) (i j : Fin 3) :
    thetaMultiplier n x i j=(if i=j then (1 : K) else -1)*thetaMultiplier n x j i := by
  have hi := hx i
  have hj := hx j
  unfold thetaMultiplier
  rw [actual_translated_root_weight n x i j hi,actual_translated_root_weight n x j i hj]
  fin_cases i <;> fin_cases j
  all_goals
    simp [rootWeight,root] at hi hj
    simp only [rootWeight,root,rootWeightNumerator,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,sub_zero,sub_neg_eq_add]
    norm_num <;> field_simp [hi,hj] <;> ring

/-- Actual function-evaluation commutator table. This alone does not
identify the theta line bundle with O(2O) or prove a Weil theorem. -/
theorem actual_theta_commutator (n x : K) (hn : n ≠ 0) (hx : AwayRoots n x) (i j : Fin 3) :
    thetaCommutator n x i j=if i=j then (1 : K) else -1 := by
  unfold thetaCommutator
  rw [actual_theta_multiplier_skew n x hx i j]
  exact mul_div_cancel_right₀ _ (actual_theta_multiplier_nonzero n x hn hx j i)

/-- The three squares retain their actual n-dependent scalar factors. -/
theorem actual_theta_square_multipliers (n x : K) (hx : AwayRoots n x) :
    thetaMultiplier n x 0 0= -3*n^2 ∧
    thetaMultiplier n x 1 1=4*n^2 ∧ thetaMultiplier n x 2 2=12*n^2 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  simp [rootWeight,root] at h0 h1 h2
  simp only [thetaMultiplier,rootWeight,root,rootTranslateX,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,sub_zero,sub_neg_eq_add]
  constructor
  · field_simp [h0] <;> ring
  constructor
  · field_simp [h1] <;> ring
  · field_simp [h2] <;> ring

end ActualTwoDescentOriginalThetaMultipliers318
