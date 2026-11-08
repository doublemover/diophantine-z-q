module
public import ThirdPeriodNormalConvergence318
public import CanonicalXModularity318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ThirdArithmeticHolomorphic318
open CanonicalXModularity318 PeriodEisenstein318 LatticeInvariants318
set_option maxHeartbeats 0

lemma standardX_formula (tau : UpperHalfPlane) :
    standardX tau=(periods tau).weierstrassP (1/3:ℂ)/(2*(Real.pi:ℂ))^2 := by
  have hz : ((3:ℕ):ℂ)⁻¹ ∉ (periods tau).lattice := by
    intro hz
    have ho := MarkedPeriod318.standardPoint_order 3 tau
    rw [MarkedPeriod318.standardPoint_formula,LatticeModelPoint318.point_of_mem tau _ hz] at ho
    change addOrderOf (0 : (ModularWeierstrass318.curve tau).toAffine.Point)=3 at ho
    simp at ho
  unfold standardX
  rw [MarkedPeriod318.standardPoint_formula,LatticeModelPoint318.point_of_notMem tau _ hz]
  simp only [LatticeModelPoint318.affinePoint,pointX,xCoord,one_div,Nat.cast_ofNat]

/-- Holomorphy of the literal standard torsion x coordinate, not a selected quartic root. -/
theorem standardX_analyticAt (tau : UpperHalfPlane) :
    AnalyticAt ℂ (fun z => standardX (UpperHalfPlane.ofComplex z)) (tau:ℂ) := by
  simp_rw [standardX_formula]
  exact (ThirdPeriodNormalConvergence318.weierstrass_analyticAt tau).div_const

/-- The actual canonical arithmetic coordinate is holomorphic on the admissible period locus. -/
theorem arithmeticX_analyticAt (tau : UpperHalfPlane)
    (h : OpenJComplexEvaluation318.Admissible tau) :
    AnalyticAt ℂ (fun z => arithmeticX (UpperHalfPlane.ofComplex z)) (tau:ℂ) := by
  have ha := (standardX_analyticAt tau).div
    (CanonicalXScale318.scale_analyticAt 1 tau h) (CanonicalXScale318.scale_ne_zero 1 tau h)
  have he : (fun z => arithmeticX (UpperHalfPlane.ofComplex z)) =ᶠ[𝓝 (tau:ℂ)]
      (fun z => standardX (UpperHalfPlane.ofComplex z)/CanonicalXScale318.scale z) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds tau.im_pos] with z hz
    have ho : UpperHalfPlane.ofComplex z=⟨z,hz⟩ := UpperHalfPlane.ofComplex_apply ⟨z,hz⟩
    rw [ho]
    rfl
  exact ha.congr he.symm

end ThirdArithmeticHolomorphic318
