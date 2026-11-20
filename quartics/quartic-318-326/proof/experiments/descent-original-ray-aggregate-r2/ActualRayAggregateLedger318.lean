module
public import Mathlib
public section
noncomputable section
namespace ActualRayAggregateLedger318

/-- Same constants as the old finite lower ledger, but only the
total signed transfer/periodic deficit is used. No rowwise norm or
other distribution premise is smuggled into the summation. -/
theorem lower_of_signed_total (α S mass meanSum : ℝ) (k W nI M N T : ℕ)
    (hα : 0<α) (hS : 0<S) (hW : 0<W)
    (hseries : (24/25:ℝ)*S≤meanSum/(α^k*(W:ℝ)^2))
    (harea : (3/25:ℝ)*((N:ℝ)*(T:ℝ))≤(nI:ℝ)*(M:ℝ)*(W:ℝ)^2)
    (transfer periodic : ℝ)
    (htransfer : transfer≤α^k*(S*((N:ℝ)*(T:ℝ)))/200)
    (hperiodic : periodic≤α^k*(S*((N:ℝ)*(T:ℝ)))/200)
    (hdefect : -(transfer+periodic)≤α^k*mass-(nI:ℝ)*(M:ℝ)*meanSum) :
    S*((N:ℝ)*(T:ℝ))/10≤mass := by
  let A := α^k*(S*((N:ℝ)*(T:ℝ)))
  have hαk : 0<α^k := pow_pos hα _
  have hW' : (0:ℝ)<(W:ℝ) := by exact_mod_cast hW
  have hA : 0≤A := by unfold A; positivity
  have hs := (le_div_iff₀ (mul_pos hαk (pow_pos hW' 2))).mp hseries
  have hAll : (72/625:ℝ)*A ≤ (nI:ℝ)*(M:ℝ)*meanSum := by
    calc
      _=((24/25:ℝ)*S*α^k)*((3/25:ℝ)*((N:ℝ)*(T:ℝ))) := by unfold A; ring
      _≤((24/25:ℝ)*S*α^k)*((nI:ℝ)*(M:ℝ)*(W:ℝ)^2) :=
        mul_le_mul_of_nonneg_left harea (by positivity)
      _=(nI:ℝ)*(M:ℝ)*(((24/25:ℝ)*S)*(α^k*(W:ℝ)^2)) := by ring
      _≤_ := mul_le_mul_of_nonneg_left hs (by positivity)
  change transfer≤A/200 at htransfer
  change periodic≤A/200 at hperiodic
  apply (mul_le_mul_left₀ hαk).mp
  calc
    _=A/10 := by unfold A; ring
    _≤_ := by linarith only [hA,hAll,htransfer,hperiodic,hdefect]

end ActualRayAggregateLedger318
