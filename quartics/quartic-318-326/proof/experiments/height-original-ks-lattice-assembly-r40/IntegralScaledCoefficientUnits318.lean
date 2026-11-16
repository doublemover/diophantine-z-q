module
public import IntegralSmoothProperBicanonical318
public import IntrinsicTensorGenerator318
public import SectionGeneratorIsomorphism318
public section
noncomputable section
namespace IntegralScaledCoefficientUnits318
open IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem J_unit (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    IsUnit (VerticalSection318.J:R) := by
  have h : (IntegralBranchDenominatorCover318.separationInteger:R)=
      (VerticalSection318.J:R)*(823200:R) := by
    norm_num [IntegralBranchDenominatorCover318.separationInteger,VerticalSection318.J]
  rw [h] at hN
  exact isUnit_of_mul_isUnit_left hN

/-- The ACTUAL J²-scaled first coefficient is a unit on each entire finite
chart. Clearing J is not harmless at excluded primes; the good-base
hypothesis proving its invertibility is retained explicitly. -/
theorem branch_zero_unit
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) (i : Fin 4) :
    IsUnit (branchCoefficient R c i 0) := by
  have hJ : IsUnit (VerticalSection318.J : IntegralBranchCoordinates318.B R c i) := by
    simpa only [map_intCast] using (J_unit R hN).map
      (algebraMap R (IntegralBranchCoordinates318.B R c i))
  simpa only [branchCoefficient,ite_true] using
    (hJ.pow 2).mul (IntegralBranchBicanonical318.coefficient0_unit R c i
      (IntegralSmoothProperBicanonical318.two_unit R hN))

/-- The ACTUAL J²-scaled second coefficient is a unit on the entire original
infinity chart, including its zero reciprocal coordinate. -/
theorem infinity_one_unit
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    IsUnit (infinityCoefficient R c 1) := by
  have hJ : IsUnit (VerticalSection318.J : IntegralInfinityChart318.Order R c) := by
    simpa only [map_intCast] using (J_unit R hN).map
      (algebraMap R (IntegralInfinityChart318.Order R c))
  simpa only [infinityCoefficient,show (1:Fin 2)≠0 by decide,ite_false] using
    (hJ.pow 2).mul (IntegralInfinityCoefficients318.coefficient1_unit R c
      (IntegralSmoothProperBicanonical318.two_unit R hN))
end IntegralScaledCoefficientUnits318
