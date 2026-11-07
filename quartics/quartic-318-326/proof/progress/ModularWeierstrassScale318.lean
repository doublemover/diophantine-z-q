module
public import ModularLattice318
public section
noncomputable section
open scoped MatrixGroups
open PeriodEisenstein318 LatticeInvariants318
namespace ModularWeierstrassScale318
open ModularLattice318
set_option maxHeartbeats 0

/-- Genuine scaling of the actual Weierstrass series, via the actual lattice bijection. -/
theorem wp_scale (g : SL(2,ℤ)) (tau : UpperHalfPlane) (z : ℂ) :
    (periods (g•tau)).weierstrassP (z/d g tau)=d g tau^2*(periods tau).weierstrassP z := by
  rw [PeriodPair.weierstrassP,PeriodPair.weierstrassP,← (latticeEquiv g tau).symm.tsum_eq,
    ← tsum_mul_left]
  apply tsum_congr
  intro l
  rw [latticeEquiv_symm_val]
  rw [← sub_div,div_pow,div_pow,div_div_eq_mul_div,div_div_eq_mul_div]
  ring

/-- Genuine scaling of the actual derivative series, with the cubic factor. -/
theorem wp_deriv_scale (g : SL(2,ℤ)) (tau : UpperHalfPlane) (z : ℂ) :
    (periods (g•tau)).derivWeierstrassP (z/d g tau)=d g tau^3*(periods tau).derivWeierstrassP z := by
  rw [PeriodPair.derivWeierstrassP,PeriodPair.derivWeierstrassP,
    ← (latticeEquiv g tau).symm.tsum_eq,mul_neg,← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro l
  rw [latticeEquiv_symm_val,← sub_div,div_pow,div_div_eq_mul_div]
  ring

theorem xCoord_scale (g : SL(2,ℤ)) (tau : UpperHalfPlane) (z : ℂ) :
    xCoord (g•tau) (z/d g tau)=d g tau^2*xCoord tau z := by
  rw [xCoord,xCoord,wp_scale]
  ring

theorem yCoord_scale (g : SL(2,ℤ)) (tau : UpperHalfPlane) (z : ℂ) :
    yCoord (g•tau) (z/d g tau)=d g tau^3*yCoord tau z := by
  rw [yCoord,yCoord,wp_deriv_scale]
  ring
end ModularWeierstrassScale318
