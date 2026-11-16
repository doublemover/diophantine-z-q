module
public import IntegralFourRootGluing318
public import OriginalIntegerReciprocalCharts318
public section
noncomputable section
namespace OriginalIntegerGluedModel318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ)

/-- An actual glued integral scheme containing the exact original integer
four-root affine order. The reciprocal chart is the proved z_i=s*y_i chart.
Properness, normalization and comparison of the complete rational fiber
with the original smooth projective model are still separate obligations. -/
abbrev model := IntegralFourRootGluing318.scheme ℤ
  (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

@[expose] def affineChart : Spec (CommRingCat.of (OriginalIntegerAffineModel318.Order c)) ⟶ model c :=
  IntegralFourRootGluing318.finiteChart ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

instance affineChart_open : IsOpenImmersion (affineChart c) :=
  IntegralFourRootGluing318.finiteChart_open ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

end OriginalIntegerGluedModel318
