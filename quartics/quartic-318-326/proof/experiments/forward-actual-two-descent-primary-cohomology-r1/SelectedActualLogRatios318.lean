module
public import ActualOrientedLogMembership318
public section
noncomputable section
namespace SelectedActualLogRatios318
open ConcreteG8Domain ConcretePadic318 ValuativeOrbitBounds318
open ActualLogHom318 ActualOrientedLogMembership318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- The actual analytic-subgroup carrier and every signed multiple are
identified, as well as the logarithm ratio. This is not a free logarithm label. -/
@[expose] def LogarithmicOrbit (hp : 19≤p) (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ) : Prop :=
  ∃ Q : formalSubgroup p hp (embedding p rho hr D)
    (ActualSplitOrbitEntry318.coefficient_integral p rho hr),
    Q.val=mappedPoint p rho hr n ∧
    ∀ j : ℤ, (j • Q).val=mappedPoint p rho hr (j*n) ∧
      logHom p hp _ _ (j • Q)/logHom p hp _ _ Q=(j:ℚ_[p])

/-- The same Pi³ CRT now produces actual integer logarithm ratios on BOTH
original elliptic groups: nH at the primary place and n(H−P) at the opposite
place. No point-membership or logarithm-homomorphism premise remains. -/
theorem selected (hp : 19≤p) (rho : ℚ_[p]) (hr : rho^2=2)
    (Pi Mminus Mplus h : ℕ) (hpPi : p∣Pi)
    (hm : SelectedQuotientOrders318.order p rho hr∣Mminus)
    (hp' : SelectedQuotientOrders318.order p (-rho) (negative_root p rho hr)∣Mplus)
    (hprimary : Nat.ModEq (Pi^3*Mminus) h 0) (hopposite : Nat.ModEq Mplus h 1)
    (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1) :
    LogarithmicOrbit p hp rho hr (h:ℤ) ∧
    LogarithmicOrbit p hp (-rho) (negative_root p rho hr) ((h:ℤ)-1) := by
  have hnearM := SelectedFormalEntry318.primary p rho hr Pi Mminus h hpPi
    (SelectedQuotientOrders318.entry_of_order_dvd p rho hr Mminus hm) hprimary 1
  have hnearP := SelectedFormalEntry318.opposite p (-rho) (negative_root p rho hr) Mplus h
    (SelectedQuotientOrders318.entry_of_order_dvd p (-rho) _ Mplus hp') hopposite 1
  simp only [one_mul] at hnearM hnearP
  constructor
  · exact integer_log_ratios p hp rho hr (h:ℤ) hzero
      ⟨weaken _ hnearM.1 (by norm_num),weaken _ hnearM.2 (by norm_num)⟩
  · exact integer_log_ratios p hp (-rho) (negative_root p rho hr) ((h:ℤ)-1)
      (sub_ne_zero.mpr hone) hnearP

end SelectedActualLogRatios318
