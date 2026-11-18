module
public import OriginalIntegerGluedModel318
public import IntegralFourRootProjectiveProper318
public section
noncomputable section
namespace OriginalIntegerProperModel318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ)

/-- The constructed integer model has an actual finite projection to the
projective line over Z. Its original integer affine chart is retained. -/
@[expose] def projection : OriginalIntegerGluedModel318.model c ⟶ ProjectiveJLine318.scheme ℤ :=
  IntegralFourRootProjectiveProjection318.projection ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

instance projection_finite : IsFinite (projection c) :=
  IntegralFourRootProjectiveProper318.projection_finite ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

@[expose] def structureMap : OriginalIntegerGluedModel318.model c ⟶ Spec (CommRingCat.of ℤ) :=
  projection c ≫ ProjectiveJLine318.structureMap ℤ

/-- A genuine proper separated arithmetic model candidate. Properness does
not imply regularity or identify its relative dualizing/cotangent lattice.
The complete rational fiber's normalization remains to be compared. -/
theorem proper_separated : IsProper (structureMap c) ∧ IsSeparated (structureMap c) :=
  IntegralFourRootProjectiveProper318.proper_separated ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

end OriginalIntegerProperModel318
