module
public import ActualTwoDescentFiniteKummerSurjectivity318
public section
noncomputable section
namespace ActualTwoDescentFiniteOriginalCompatibility318
set_option maxHeartbeats 16000000

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- The good-characteristic model is literally the original model, not an auxiliary curve. -/
lemma actual_same_curve (n : K) : ActualTwoDescentFiniteEllipticModel318.curve n=
    ActualTwoDescentEllipticModel318.curve n := rfl

lemma actual_same_first_root_coordinate (n : K) (hn : n ≠ 0)
    (P : ActualTwoDescentEllipticModel318.Point n) :
    ActualTwoDescentFiniteSimpleRootCoordinates318.rootCoordinate
      (ActualTwoDescentFiniteSimpleRootCoordinates318.firstRoot n hn) P=
    ActualTwoDescentSimpleRootCoordinates318.rootCoordinate
      (ActualTwoDescentSimpleRootCoordinates318.firstRoot n hn) P := by
  cases P <;> rfl

lemma actual_same_second_root_coordinate (n : K) (hn : n ≠ 0)
    (P : ActualTwoDescentEllipticModel318.Point n) :
    ActualTwoDescentFiniteSimpleRootCoordinates318.rootCoordinate
      (ActualTwoDescentFiniteSimpleRootCoordinates318.secondRoot n hn) P=
    ActualTwoDescentSimpleRootCoordinates318.rootCoordinate
      (ActualTwoDescentSimpleRootCoordinates318.secondRoot n hn) P := by
  cases P <;> rfl

lemma actual_same_kummer_class (n : K) (hn : n ≠ 0)
    (P : ActualTwoDescentEllipticModel318.Point n) :
    ActualTwoDescentFiniteKummerHom318.kummerClass n hn P=
    ActualTwoDescentKummerHom318.kummerClass n hn P := by
  cases P <;> rfl

end ActualTwoDescentFiniteOriginalCompatibility318
