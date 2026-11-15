module
public import ActualAnchorRatio318
public section
noncomputable section
namespace PreparedAnchorLabels318
open ScalarPreparedResidues318 FixedArithmeticLabels318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The additional3-power is chosen before the fixed labels. It leaves the
free positive multiplier available and does not change either Lucas relation. -/
@[expose] def multiplier (N d : ℕ) : ℕ := 3^N*d
lemma multiplier_ne (N d : ℕ) (hd : d≠0) : multiplier N d≠0 := by
  exact mul_ne_zero (by positivity) hd

lemma scalar_depth (A B N d : ℕ) (hd : d≠0) :
    N≤padicValInt 3 (scalarLabel A B (multiplier N d)-1) := by
  have h3 : padicValNat 3 6=1 := by
    rw [show (6:ℕ)=3*2 by norm_num,padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self,padicValNat_primes (by decide : 3≠2)]
    norm_num
  have he : scalarLabel A B (multiplier N d)-1=
      ((6^(A+B+15)*(3^N*d):ℕ):ℤ) := by simp [scalarLabel,multiplier]
  rw [he,padicValInt.of_nat,
    padicValNat.mul (by positivity : (6:ℕ)^(A+B+15)≠0) (multiplier_ne N d hd),
    padicValNat.mul (by positivity : (3:ℕ)^N≠0) hd,
    padicValNat.pow,padicValNat.prime_pow,h3]
  omega

/-- Actual chosen labels meet the physical-anchor local depth conditions for
any prescribed power3^N, including the current enormous fixed anchor. -/
theorem actual_anchor_depths (a : ℤ) (A B N d : ℕ) (hd : d≠0) :
    let ns := FixedArithmeticLabels318.labels a A B (multiplier N d) (multiplier_ne N d hd)
    ActualAnchorRatio318.ratio ns N≠0 ∧
      padicValRat 2 (ActualAnchorRatio318.ratio ns N)=0 ∧
      0≤padicValRat 3 (ActualAnchorRatio318.ratio ns N) := by
  dsimp only
  apply ActualAnchorRatio318.local_depths _
    (FixedArithmeticLabels318.labels_odd a A B _ (multiplier_ne N d hd))
  · have hs := (ScalarPreparedResidues318.label_domains A B _ (multiplier_ne N d hd)).1
    change scalarLabel A B (multiplier N d)≠1
    omega
  · have hs := scalar_depth A B N d hd
    change (N:ℤ)≤2+2*(padicValInt 3 (scalarLabel A B (multiplier N d)-1):ℤ)
    omega

end PreparedAnchorLabels318
