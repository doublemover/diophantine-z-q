module
public import ActualReciprocalParameters318
public section
noncomputable section
namespace ActualPrimaryLogPrecision318
open ActualLogHom318 ActualLogIdentification318 ActualLogRatio318
open ConcreteG8Domain ConcretePadic318 CoherentMultipleCharts318 ActualOrientedLogMembership318
open ActualReciprocalParameters318 ValuativeOrbitBounds318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

lemma integer_bound (n : ℤ) : Bound Padic.addValuation 0 (n:ℚ_[p]) := by
  cases n with
  | ofNat n => exact bnat _ n
  | negSucc n => simpa only [Int.cast_negSucc] using bneg Padic.addValuation (bnat _ (n+1))

/-- The actual integer logarithm ratio forces the original z-ratio to be
integral. No assumption about a quotient's valuation is supplied. -/
lemma z_ratio_integral (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P Q : formalSubgroup p hp D hD) (n : ℤ)
    (hn : logHom p hp D hD P/logHom p hp D hD Q=(n:ℚ_[p])) :
    Bound Padic.addValuation 0 (zParameter p D P.val/zParameter p D Q.val) := by
  have he : Padic.addValuation (zParameter p D P.val/zParameter p D Q.val)=
      Padic.addValuation (n:ℚ_[p]) := by
    rw [Padic.addValuation.map_div,←logHom_z_valuation p hp D hD P,
      ←logHom_z_valuation p hp D hD Q,←Padic.addValuation.map_div,hn]
  change (0:WithTop ℤ)≤_
  rw [he]
  exact integer_bound p n

/-- All primary integer labels are approximated to four times the actual
common chart depth. Both source points are the original n*h and h. -/
theorem original_ratio (hp : 19≤p) (rho : ℚ_[p]) (hr : rho^2=2)
    (h7 : ¬p∣49) (h n R : ℤ) (hzero : h≠0) (hnzero : n≠0) (hR : 1≤R)
    (hbase : Near (place p rho hr) R (chartU h) (chartV h))
    (hmult : Near (place p rho hr) R (chartU (n*h)) (chartV (n*h))) :
    Bound (place p rho hr) (4*R)
      ((-chartU (n*h)/chartV (n*h))/(-chartU h/chartV h)-(n:K)) := by
  let σ := embedding p rho hr
  let Dp := σ ConcreteG8Domain.D
  have hnear : Near (place p rho hr) 1 (chartU h) (chartV h) :=
    ⟨weaken _ hbase.1 hR,weaken _ hbase.2 hR⟩
  obtain ⟨Q,hQ,hall⟩ := integer_log_ratios p hp rho hr h hzero hnear
  let P := n • Q
  have hP : P.val=mappedPoint p rho hr (n*h) := (hall n).1
  have hlog : logHom p hp Dp _ P/logHom p hp Dp _ Q=(n:ℚ_[p]) := (hall n).2
  have huP : σ (chartU (n*h))≠0 := mapped_u_ne p rho hr _ (mul_ne_zero hnzero hzero)
  have huQ : σ (chartU h)≠0 := mapped_u_ne p rho hr _ hzero
  let r := (σ (chartU (n*h))).valuation
  let s := (σ (chartU h)).valuation
  have hrR : R≤r := finite_depth_ge p _ huP R hmult.1
  have hsR : R≤s := finite_depth_ge p _ huQ R hbase.1
  have hDp : Padic.addValuation Dp=0 := coefficient_unit p rho hr h7
  have hwP : wParameter p Dp P.val=0 ∨ (wParameter p Dp P.val).valuation=4*r := by
    right
    rw [hP,mapped_w,map_mul,map_pow]
    exact argument_depth p Dp _ hDp huP
  have hwQ : wParameter p Dp Q.val=0 ∨ (wParameter p Dp Q.val).valuation=4*s := by
    right
    rw [hQ,mapped_w,map_mul,map_pow]
    exact argument_depth p Dp _ hDp huQ
  have he := first_order_ratio_precision p hp Dp _ P Q r s (by omega) (by omega) hwP hwQ
  have hi := z_ratio_integral p hp Dp _ P Q n hlog
  have hbound : ((4*R:ℤ):WithTop ℤ)≤Padic.addValuation
      (logHom p hp Dp _ P/logHom p hp Dp _ Q-zParameter p Dp P.val/zParameter p Dp Q.val) := by
    apply le_trans _ he
    calc
      ((4*R:ℤ):WithTop ℤ) ≤ ((4*min r s:ℤ):WithTop ℤ) := by
        exact_mod_cast (show 4*R≤4*min r s by omega)
      _ ≤ Padic.addValuation (zParameter p Dp P.val/zParameter p Dp Q.val)+
          ((4*min r s:ℤ):WithTop ℤ) := le_add_of_nonneg_left hi
  rw [hlog,hP,hQ,mapped_z,mapped_z] at hbound
  have he := bneg Padic.addValuation hbound
  change ((4*R:ℤ):WithTop ℤ)≤Padic.addValuation (σ _)
  simpa only [map_sub,map_div₀,map_intCast,neg_sub] using he

end ActualPrimaryLogPrecision318
