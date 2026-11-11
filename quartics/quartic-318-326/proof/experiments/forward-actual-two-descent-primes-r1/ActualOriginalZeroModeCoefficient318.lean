module
public import ActualOriginalRationalPoisson318
public section
noncomputable section
namespace ActualOriginalZeroModeCoefficient318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCoordinateFrequency318
open ActualOriginalRationalPoisson318 ActualOriginalUnitFourierLayers318
open ActualOriginalGlobalCoefficient318
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma actual_complete_arc_zero (κ : ℤ) (q : ℕ) [NeZero q] (a : ℤ) :
    completeArcCoefficient κ q a 0 =
      ∑ r : Coordinates (ZMod q), ZMod.stdAddChar ((a : ZMod q)*equation (κ : ZMod q) r) := by
  simp [completeArcCoefficient,integerEmbed_zero,actual_frequency_apply,dot]

/-- The zero-mode unit numerator sum is exactly the already constructed
q^-5 global singular-series coefficient, including modulus1. -/
theorem actual_zero_mode_coefficient (κ : ℤ) (q : ℕ) [NeZero q] :
    (∑ a : {a : ZMod q // IsUnit a},
      completeArcCoefficient κ q (a.val.val : ℤ) 0) / (q : ℂ)^5 = coefficient κ q := by
  classical
  rw [actual_coefficient_nonzero]
  simp only [actual_complete_arc_zero,Int.cast_natCast,ZMod.natCast_val]
  rfl

end ActualOriginalZeroModeCoefficient318
