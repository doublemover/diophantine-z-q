module
public import AffineIdealCoordinates318
public section
noncomputable section
namespace ThreeJReciprocalKernelSupport318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJGlobalRamificationScheme318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual global kernel restricted to the original reciprocal chart,
then expressed through canonical affine global sections. -/
@[expose] def reciprocalCoordinateIdeal : Ideal ℚ[X] :=
  AffineIdealCoordinates318.coordinates (ideal.comap (JLineAtlas318.chart ℚ 0))

/-- Every scheme prime in the actual reciprocal kernel is in its punctured
open. This derives from the genuine global closed immersion and the original
projective chart intersection, not an analytic-point or support guess. -/
theorem support_punctured :
    PrimeSpectrum.zeroLocus (reciprocalCoordinateIdeal : Set ℚ[X]) ⊆ PrimeSpectrum.basicOpen X := by
  intro p hp
  change p ∈ PrimeSpectrum.zeroLocus
    (AffineIdealCoordinates318.coordinates (ideal.comap (JLineAtlas318.chart ℚ 0)) : Set ℚ[X]) at hp
  rw [←AffineIdealCoordinates318.support_coordinates] at hp
  have hg : JLineAtlas318.chart ℚ 0 p ∈ (ideal.support : Set _) := by
    simpa only [Scheme.IdealSheafData.support_comap] using hp
  have hf := support_in_finite_chart hg
  change p ∈ JLineAtlas318.chart ℚ 0 ⁻¹ᵁ (JLineAtlas318.chart ℚ 1).opensRange at hf
  rw [ProjectiveLinePointEquiv318.chart_zero_preimage_one] at hf
  exact hf

/-- The actual reciprocal ideal is saturated at X with its full
nilpotent structure: X is an actual unit in its quotient algebra. -/
theorem actual_coordinate_unit : IsUnit (Ideal.Quotient.mk reciprocalCoordinateIdeal (X:ℚ[X])) :=
  AffineIdealCoordinates318.quotient_unit_of_support reciprocalCoordinateIdeal X support_punctured
end ThreeJReciprocalKernelSupport318
