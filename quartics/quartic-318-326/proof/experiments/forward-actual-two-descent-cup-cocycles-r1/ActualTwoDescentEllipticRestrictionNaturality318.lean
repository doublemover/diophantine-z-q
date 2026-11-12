module
public import ActualTwoDescentCocycleRestrictionCoordinates318
public section
noncomputable section
namespace ActualTwoDescentEllipticRestrictionNaturality318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentActualEllipticFieldMap318
open ActualTwoDescentKummerFieldNaturality318 ActualTwoDescentSquareClassFieldMap318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldContinuousTorsionCoordinates318
open ActualTwoDescentFieldCocycleSquareclassCompatibility318 ActualTwoDescentContinuousCocycleRestriction318
open ActualTwoDescentCocycleRestrictionCoordinates318 ActualTwoDescentFieldActualCohomologicalImage318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]

/-- Actual elliptic connecting maps commute with actual Galois restriction at EVERY point, including torsion. -/
theorem actual_elliptic_restriction_naturality (f : F →+* L) (n : F) (hn : n ≠ 0) (P : Point n) :
    cocycleRestriction f n hn (continuousConnectingHom n hn (Multiplicative.ofAdd P))=
      continuousConnectingHom (f n) (field_map_ne_zero f hn)
        (Multiplicative.ofAdd (ellipticFieldMap f n hn P)) := by
  apply (continuousTorsionSquareclasses (f n) (field_map_ne_zero f hn)).injective
  rw [actual_cocycle_restriction_squareclasses,actual_cocycle_squareclass_compatibility,
    actual_cocycle_squareclass_compatibility]
  exact (actual_kummer_field_naturality f n hn P).symm

lemma actual_rational_cocycle_image_restricts (f : F →+* L) (n : F) (hn : n ≠ 0) :
    rationalCocycleImage n hn ≤ (rationalCocycleImage (f n) (field_map_ne_zero f hn)).comap (cocycleRestriction f n hn) := by
  rintro χ ⟨P,rfl⟩
  exact ⟨Multiplicative.ofAdd (ellipticFieldMap f n hn P.toAdd),(actual_elliptic_restriction_naturality f n hn P.toAdd).symm⟩

end ActualTwoDescentEllipticRestrictionNaturality318
