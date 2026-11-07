module
public import LatticeModelPoint318
public section
noncomputable section
namespace TorusPointInterface318
open PeriodEisenstein318 LatticeInvariants318 LatticeModelPoint318 ModularWeierstrass318
set_option maxHeartbeats 0

theorem point_eq_zero_iff (tau : UpperHalfPlane) (z : ℂ) :
    point tau z = 0 ↔ z ∈ (periods tau).lattice := by
  constructor
  · intro h
    by_contra hz
    rw [point_of_notMem tau z hz] at h
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ h
  · exact point_of_mem tau z

theorem point_neg (tau : UpperHalfPlane) (z : ℂ) :
    point tau (-z) = - point tau z := by
  have hm : -z ∈ (periods tau).lattice ↔ z ∈ (periods tau).lattice := neg_mem_iff
  by_cases hz : z ∈ (periods tau).lattice
  · rw [point_of_mem tau z hz, point_of_mem tau (-z) (hm.mpr hz)]
    rfl
  · have hnz : -z ∉ (periods tau).lattice := fun h => hz (hm.mp h)
    rw [point_of_notMem tau z hz, point_of_notMem tau (-z) hnz]
    rw [WeierstrassCurve.Affine.Point.neg_def]
    simp [WeierstrassCurve.Affine.Point.neg, affinePoint, xCoord, yCoord, PeriodPair.weierstrassP_neg,
      PeriodPair.derivWeierstrassP_neg, neg_div,
      WeierstrassCurve.Affine.negY, curve, NormalizedWeierstrass318.model]

theorem torusPoint_eq_zero_iff (tau : UpperHalfPlane)
    (q : ℂ ⧸ (periods tau).lattice.toAddSubgroup) :
    torusPoint tau q = 0 ↔ q = 0 := by
  induction q using Quotient.inductionOn with
  | h z =>
    rw [torusPoint_mk, point_eq_zero_iff]
    exact (QuotientAddGroup.eq_zero_iff (N := (periods tau).lattice.toAddSubgroup) z).symm

theorem torusPoint_neg (tau : UpperHalfPlane)
    (q : ℂ ⧸ (periods tau).lattice.toAddSubgroup) :
    torusPoint tau (-q) = - torusPoint tau q := by
  induction q using Quotient.inductionOn with
  | h z =>
    change point tau (-z) = - point tau z
    exact point_neg tau z

end TorusPointInterface318
