module
public import FifthGlobalPullbackNormalization318
public section
noncomputable section
namespace FiveActualPullbacksIndependent318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open scoped BigOperators
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- Rational independence of five actual completed elliptic quotient
invariant pullbacks in the genuine global intrinsic differential space. -/
theorem independent (a:Fin 4→ℚ) (b:ℚ)
    (h:(∑i,ContactCharacterGlobalIndependence318.constants (a i) •
      ContactCharacterDifferentials318.differential i)+
        ContactCharacterGlobalIndependence318.constants b • FifthActualDifferential318.differential=0):
    (∀i,a i=0) ∧ b=0:=by
  rw [FifthGlobalPullbackNormalization318.global_eq,smul_smul,←map_mul] at h
  have hh:=FifthGlobalIndependence318.independent a (b*FifthInvariantScalar318.scale) h
  exact ⟨hh.1,(mul_eq_zero.mp hh.2).resolve_right (by norm_num [FifthInvariantScalar318.scale])⟩

theorem fifth_nonzero:FifthActualDifferential318.differential≠0:=by
  intro hz
  have h:(∑i:Fin 4,ContactCharacterGlobalIndependence318.constants (0:ℚ) •
      ContactCharacterDifferentials318.differential i)+
        ContactCharacterGlobalIndependence318.constants 1 • FifthActualDifferential318.differential=0:=by
    simp only [map_zero,zero_smul,Finset.sum_const_zero,hz,smul_zero,add_zero]
  exact one_ne_zero (independent (fun _=>0) 1 h).2
end FiveActualPullbacksIndependent318
