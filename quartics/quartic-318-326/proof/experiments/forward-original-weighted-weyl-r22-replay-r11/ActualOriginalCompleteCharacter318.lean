module
public import ActualOriginalUnitGaussBound318
public section
noncomputable section
namespace ActualOriginalCompleteCharacter318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCoordinateFrequency318
open ActualOriginalPeriodizationCoefficient318 ActualOriginalResidueLattice318
open ActualOriginalRationalPoisson318
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def linearResidue (q : ℕ) (m : Coordinates ℤ) (r : Coordinates (ZMod q)) : ZMod q :=
  (m.1.1 : ZMod q)*r.1.1+(m.1.2 : ZMod q)*r.1.2+
    (m.2.1.1 : ZMod q)*r.2.1.1+(m.2.1.2 : ZMod q)*r.2.1.2+(m.2.2 : ZMod q)*r.2.2

lemma actual_residue_linear_cast (q : ℕ) [NeZero q]
    (m : Coordinates ℤ) (r : Coordinates (ZMod q)) :
    (integerDot m (residueLift q r) : ZMod q) = linearResidue q m r := by
  simp [integerDot,residueLift,linearResidue]

/-- The positive real residue character in actual Poisson is precisely
the standard modular character of the original full integer dot product. -/
lemma actual_residue_linear_character (q : ℕ) [NeZero q]
    (m : Coordinates ℤ) (r : Coordinates (ZMod q)) :
    (Real.fourierChar (frequency (integerEmbed m) (integerEmbed (residueLift q r))/(q : ℝ)) : ℂ) =
      ZMod.stdAddChar (linearResidue q m r) := by
  rw [actual_integer_frequency,←actual_residue_linear_cast,ZMod.stdAddChar_coe,Real.fourierChar_apply]
  push_cast
  congr 1
  ring

/-- Literal modular form of the actual five-coordinate complete arc
coefficient, retaining the positive linear term from Poisson. -/
theorem actual_complete_arc_modular (κ : ℤ) (q : ℕ) [NeZero q]
    (a : ℤ) (m : Coordinates ℤ) :
    completeArcCoefficient κ q a m =
      ∑ r : Coordinates (ZMod q),
        ZMod.stdAddChar ((a : ZMod q)*equation (κ : ZMod q) r+linearResidue q m r) := by
  unfold completeArcCoefficient
  simp_rw [actual_residue_linear_character,←AddChar.map_add_eq_mul]

end ActualOriginalCompleteCharacter318
