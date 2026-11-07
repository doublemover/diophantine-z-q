module
public import LatticeInvariants318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
noncomputable section
namespace LatticeModelPoint318
open LatticeInvariants318 PeriodEisenstein318 ModularWeierstrass318
set_option maxHeartbeats 0

theorem actual_equation (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) :
    (curve tau).toAffine.Equation (xCoord tau z) (yCoord tau z) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa [curve, NormalizedWeierstrass318.model, sub_eq_add_neg, neg_div, mul_assoc]
    using normalized_weierstrass_equation tau z hz

theorem actual_nonsingular (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) :
    (curve tau).toAffine.Nonsingular (xCoord tau z) (yCoord tau z) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (curve_discriminant_ne_zero tau)).mp (actual_equation tau z hz)

/-- The actual lattice Weierstrass functions now yield an actual point of
the normalized elliptic model, away from the period lattice. -/
@[expose] def affinePoint (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) : (curve tau).toAffine.Point :=
  WeierstrassCurve.Affine.Point.some (xCoord tau z) (yCoord tau z)
    (actual_nonsingular tau z hz)

/-- Period-lattice arguments are assigned the actual point at infinity.
No bijectivity or group-uniformization claim is part of this construction. -/
@[expose] def point (tau : UpperHalfPlane) (z : ℂ) : (curve tau).toAffine.Point := by
  classical
  exact if hz : z ∈ (periods tau).lattice then .zero else affinePoint tau z hz

theorem point_of_mem (tau : UpperHalfPlane) (z : ℂ) (hz : z ∈ (periods tau).lattice) :
    point tau z = .zero := by
  simp [point,hz]

theorem point_of_notMem (tau : UpperHalfPlane) (z : ℂ) (hz : z ∉ (periods tau).lattice) :
    point tau z = affinePoint tau z hz := by
  simp [point,hz]

/-- The actual analytic point construction is invariant under every period. -/
theorem point_add_period (tau : UpperHalfPlane) (z : ℂ) (l : (periods tau).lattice) :
    point tau (z+l) = point tau z := by
  have hm : z + (l : ℂ) ∈ (periods tau).lattice ↔ z ∈ (periods tau).lattice :=
    add_mem_cancel_right l.property
  by_cases hz : z ∈ (periods tau).lattice
  · rw [point_of_mem tau z hz, point_of_mem tau (z+l) (hm.mpr hz)]
  · have hzl : z+(l:ℂ) ∉ (periods tau).lattice := fun h => hz (hm.mp h)
    rw [point_of_notMem tau z hz, point_of_notMem tau (z+l) hzl]
    simp [affinePoint, xCoord, yCoord, PeriodPair.weierstrassP_add_coe,
      PeriodPair.derivWeierstrassP_add_coe]

/-- A genuine map from the actual complex period quotient to actual elliptic
points. This is not yet a bijection or an additive-homomorphism theorem. -/
@[expose] def torusPoint (tau : UpperHalfPlane) :
    (ℂ ⧸ (periods tau).lattice.toAddSubgroup) → (curve tau).toAffine.Point :=
  Quotient.lift (point tau) (by
    intro z w h
    have hm : -z+w ∈ (periods tau).lattice := QuotientAddGroup.leftRel_apply.mp h
    have hp := point_add_period tau z ⟨-z+w,hm⟩
    simpa using hp.symm)

theorem torusPoint_mk (tau : UpperHalfPlane) (z : ℂ) :
    torusPoint tau (QuotientAddGroup.mk z) = point tau z := rfl

end LatticeModelPoint318
