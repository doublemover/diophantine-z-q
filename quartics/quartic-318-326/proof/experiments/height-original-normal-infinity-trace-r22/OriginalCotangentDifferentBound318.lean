module
public import OriginalCotangentCoordinateTransfer318
public import OriginalNormalizationCotangentDiscrepancy318
public section
noncomputable section
namespace OriginalCotangentDifferentBound318
open NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalizationConductorSpecialization318 OriginalNormalizationDifferentValue318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)
local notation "H" => OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M
local notation "δ" => differentValue c t w D M

include ht in
/-- All integral coefficients lie in the OLD actual cotangent image,
using its now proved dt membership, not an assumed unit lattice. -/
theorem integral_mem (z : K c t) (hz : w z ≤ 1) : z ∈ H := by
  let r : V c t w := ⟨z,(ActualFinitePlaceIntegers318.bounded_iff w z).mp hz⟩
  have h := H.smul_mem r (OriginalCotangentCoordinateTransfer318.one_mem c t w D M ht)
  simpa only [Algebra.smul_def,mul_one] using h

include ht in
/-- The actual specialized conductor lies in the OLD cotangent image.
This is a one-sided inclusion and does not identify either with Hodge. -/
theorem conductor_le : conductorValues c t w D M ≤ H := by
  intro z hz
  exact integral_mem c t w D M ht z
    (OriginalNormalizationIntegralEvaluation318.conductorValues_bounded c t w D M ht z hz)

include ht in
/-- Multiplication by the SAME evaluated raw different sends EVERY
actual normalized-codifferent coefficient into the actual cotangent image. -/
theorem different_mul_mem (z : K c t) (hz : z ∈ codifferentValues c t w D M) : δ*z ∈ H :=
  conductor_le c t w D M ht ((mem_iff_conductor c t w D M z).mp hz)

/-- A genuine produced denominator-corrected discrepancy bound. It
retains δ; the uncorrected ratio bound and regular-model discrepancy are
not asserted. All quantities are in the SAME original dt coordinate. -/
theorem corrected_ratio_bound :
    w (δ * OriginalNormalizationCotangentDiscrepancy318.ratio c t w D M ht) ≤ 1 := by
  let b := OriginalNormalizationCotangentDiscrepancy318.generator c t w D M ht
  have hb : b ∈ codifferentValues c t w D M := by
    rw [OriginalNormalizationCotangentDiscrepancy318.image_eq c t w D M ht]
    refine ⟨1,?_⟩
    change algebraMap (V c t w) (K c t) 1 * b=b
    rw [map_one,one_mul]
  have h := (OriginalNormalCenterPrincipalImage318.mem_iff_norm c t w D M (δ*b)).mp
    (different_mul_mem c t w D M ht b hb)
  simpa only [OriginalNormalizationCotangentDiscrepancy318.ratio,
    div_eq_mul_inv,map_mul,map_inv₀,mul_assoc] using h

include ht in
/-- The same raw-different correction gives integral pairing with the
FULL actual cotangent dual, not merely its selected generator. -/
theorem corrected_pairing (z : K c t) (hz : z ∈ codifferentValues c t w D M)
    (q : K c t) (hq : q ∈ OriginalNormalCenterDualImage318.dual c t w D M) :
    w (q*(δ*z)) ≤ 1 :=
  (integral_pairing_iff c t w D M (δ*z)).mpr
    (different_mul_mem c t w D M ht z hz) q hq
end OriginalCotangentDifferentBound318
