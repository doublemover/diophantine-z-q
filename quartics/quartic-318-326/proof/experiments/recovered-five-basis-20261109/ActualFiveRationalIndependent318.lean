module
public import FiveActualPullbacksIndependent318
public import ActualQuotientConstantPullback318
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Fintype.Option

public section
noncomputable section
namespace ActualFiveRationalIndependent318
open AlgebraicGeometry SourceTwistArithmetic318
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

abbrev M := ContactIntrinsicDifferentials318.omega units
abbrev G := Γ(M, ⊤)

/-- Restriction of scalars along the original source structural constant map.
No alternative action on the original differential space is introduced. -/
@[expose, instance_reducible] def rationalModule : Module ℚ G :=
  Module.compHom G ActualQuotientConstantPullback318.sourceConstant

attribute [local instance] rationalModule

theorem rational_smul (a : ℚ) (s : G) :
    a • s = ActualQuotientConstantPullback318.sourceConstant a • s := rfl

theorem original_constant (a : ℚ) :
    ActualQuotientConstantPullback318.sourceConstant a =
      ContactCharacterGlobalIndependence318.constants a := rfl

/-- `none` is the fifth actual pullback, and `some i` is the original
completed complementary quotient pullback for index `i`. -/
@[expose] def differential : Option (Fin 4) → G
  | none => FifthActualDifferential318.differential
  | some i => ContactCharacterDifferentials318.differential i

/-- The five already constructed whole-scheme pullbacks are independent
for exactly the original structural rational scalar action. -/
theorem independent : LinearIndependent ℚ differential := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have h : (∑ i : Fin 4, ContactCharacterGlobalIndependence318.constants (a (some i)) •
      ContactCharacterDifferentials318.differential i) +
      ContactCharacterGlobalIndependence318.constants (a none) •
      FifthActualDifferential318.differential = 0 := by
    rw [Fintype.sum_option] at ha
    change ContactCharacterGlobalIndependence318.constants (a none) •
      FifthActualDifferential318.differential +
      (∑ i : Fin 4, ContactCharacterGlobalIndependence318.constants (a (some i)) •
        ContactCharacterDifferentials318.differential i) = 0 at ha
    rw [add_comm] at ha
    exact ha
  have hzero := FiveActualPullbacksIndependent318.independent (fun i => a (some i)) (a none) h
  intro i
  cases i with
  | none => exact hzero.2
  | some i => exact hzero.1 i

end ActualFiveRationalIndependent318
