module
public import ActualCasselsTateNativeContinuousUnitComparison318
public import ActualCasselsTateRealDetectionConsumer318
public section
noncomputable section
namespace ActualCasselsTateNativeMilneDefect318
open ActualCasselsTateNativeContinuousUnitComparison318 ActualCasselsTateRealDetectionConsumer318
open ActualCasselsTateContinuousThirdObstruction318 ActualCasselsTateUnitCoefficients318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentTorsionIntoFullCocycles318 ActualTwoDescentActualShaDefinition318

/-- Consequence of finite binary real detection for the very same native
degree-three unit class. The global arithmetic theorem is an explicit input. -/
theorem nativeDefect_zero_of_real_detection (hdetect : RealDetectsBinaryThree)
    (n : ℚ) (hn : n ≠ 0) (χ ψ : continuousCocycles n)
    (hSha : fullClassHom n hn (torsionFullCocycle n hn χ) ∈ actualSha n hn) :
    nativeUnitThreeClass (continuousDefect n hn χ ψ) = 0 := by
  apply (nativeDefect_eq_zero_iff n hn χ ψ).mpr
  apply (actualThirdObstruction_eq_one_iff n hn χ ψ).mpr
  obtain ⟨b,_,_,hbc,hd⟩ := actual_global_primitive_of_real_detection hdetect n hn χ ψ hSha
  exact ⟨fun x y => binaryUnit (b x y),hbc,hd⟩
end ActualCasselsTateNativeMilneDefect318
