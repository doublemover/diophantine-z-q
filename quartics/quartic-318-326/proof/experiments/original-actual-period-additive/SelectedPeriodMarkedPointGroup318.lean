module
public import SelectedPeriodPointGroup318
public import SelectedGenuinePeriodMark318
public section
noncomputable section

namespace SelectedPeriodMarkedPointGroup318
open SelectedGenuinePeriodMark318 SelectedPeriodPointGroup318

/-- The same explicitly constructed rational period mark, now in
the genuine elliptic point group with its independent addition. -/
@[expose] def markPoint (N : ℕ) (τ : UpperHalfPlane) : (curve (period τ)).toAffine.Point :=
  additiveUniformization (period τ) (markedTorus N τ)

theorem markPoint_raw (N : ℕ) (τ : UpperHalfPlane) :
    markPoint N τ = rawPoint (period τ) (liftMark N) :=
  pointHom_mk (period τ) (liftMark N)

theorem markPoint_coords (N : ℕ) (τ : UpperHalfPlane) (hN : 1 < N) :
    markPoint N τ = .some (markX N τ) (markY N τ)
      (nonsingular (period τ) (liftMark N) (liftMark_nonperiod τ N hN)) := by
  rw [markPoint_raw]
  exact rawPoint_nonperiod _ _ (liftMark_nonperiod τ N hN)

theorem exact_order_test (N k : ℕ) (τ : UpperHalfPlane) (hN : N ≠ 0) :
    k • markPoint N τ = 0 ↔ N ∣ k := by
  let e := additiveUniformization (period τ)
  change k • e (markedTorus N τ) = 0 ↔ N ∣ k
  rw [← map_nsmul]
  constructor
  · intro h
    apply (markedTorus_nsmul_eq_zero_iff τ N k hN).mp
    exact e.injective (h.trans (map_zero e).symm)
  · intro h
    rw [(markedTorus_nsmul_eq_zero_iff τ N k hN).mpr h,map_zero]

end SelectedPeriodMarkedPointGroup318

#print axioms SelectedPeriodMarkedPointGroup318.markPoint_coords
#print axioms SelectedPeriodMarkedPointGroup318.exact_order_test
