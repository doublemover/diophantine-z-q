module
public import FourRootOrderLocalizationMaps318
public import OriginalIntegerReciprocalCharts318
public import IntegralFourRootScalarMaps318
public section
noncomputable section
namespace OriginalIntegerReciprocalOrderOverlap318
open Polynomial
variable (c : Fin 4 → ℚˣ)
abbrev Laurent := IntegralWholeReciprocalOverlap318.Laurent ℤ
abbrev Order := OriginalIntegerReciprocalCharts318.ReciprocalOrder c
abbrev CommonOrder := IntegralFourRootOverlap318.CommonOrder ℤ
  (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

/-- The existing reciprocal root-scaled map, not a newly chosen field embedding. -/
@[expose] def infinityMap : Order c →+* CommonOrder c :=
  IntegralFourRootOverlap318.infinityMap ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts

@[expose] def commonAlgebra : Algebra (Order c) (CommonOrder c) :=
  (infinityMap c).toAlgebra
attribute [local instance] commonAlgebra

/-- Select s=1/t only on the polynomial-to-Laurent leg. The common order
and its Laurent action were defined before this selection and remain unchanged. -/
local instance reciprocalLaurentAlgebra : Algebra ℤ[X] Laurent :=
  (IntegralFourRootOverlap318.reciprocalMap ℤ).toRingHom.toAlgebra
local instance reciprocalLocalization : IsLocalization.Away (X : ℤ[X]) Laurent :=
  IntegralWholeReciprocalLocalization318.reciprocal_localization ℤ (fun _ => 1)

/-- The generic localization map specializes to the exact existing infinityMap,
including the same full four-root scaling equivalence on the common order. -/
theorem map_identity :
    FourRootOrderLocalizationMaps318.map (A := ℤ[X]) (T := Laurent) (C := CommonOrder c)
      (IntegralFourRootReciprocalCharts318.reciprocalCoefficient
        (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts)
      (IntegralFourRootOverlap318.fullOverlap ℤ
        (OriginalIntegerReciprocalCharts318.integralTwist c)
        OriginalIntegerAffineModel318.contacts).toRingEquiv = infinityMap c := rfl

/-- The actual common order is the reciprocal order with only its chart
parameter inverted. No integer, twist coefficient or root is inverted. -/
theorem localization :
    IsLocalization.Away (algebraMap ℤ[X] (Order c) X) (CommonOrder c) := by
  exact FourRootOrderLocalizationMaps318.localization
    (A := ℤ[X]) (T := Laurent) (C := CommonOrder c)
    (IntegralFourRootReciprocalCharts318.reciprocalCoefficient
      (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts)
    (IntegralFourRootOverlap318.fullOverlap ℤ
      (OriginalIntegerReciprocalCharts318.integralTwist c)
      OriginalIntegerAffineModel318.contacts).toRingEquiv (X : ℤ[X])

/-- Injectivity uses the coefficient-domain/free-order argument, not an
unproved domain or normality premise for the reciprocal order. -/
theorem infinityMap_injective : Function.Injective (infinityMap c) := by
  exact FourRootOrderLocalizationMaps318.map_injective
    (A := ℤ[X]) (T := Laurent) (C := CommonOrder c)
    (IntegralFourRootReciprocalCharts318.reciprocalCoefficient
      (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts)
    (IntegralFourRootOverlap318.fullOverlap ℤ
      (OriginalIntegerReciprocalCharts318.integralTwist c)
      OriginalIntegerAffineModel318.contacts).toRingEquiv (X : ℤ[X]) Polynomial.X_ne_zero

/-- The literal coefficient square records the reciprocal polynomial action,
while keeping the original finite Laurent action on the common order. -/
theorem polynomial (p : ℤ[X]) :
    infinityMap c (algebraMap ℤ[X] (Order c) p) =
      algebraMap Laurent (CommonOrder c) (IntegralFourRootOverlap318.reciprocalMap ℤ p) :=
  IntegralFourRootScalarMaps318.infinity_polynomial ℤ
    (OriginalIntegerReciprocalCharts318.integralTwist c) OriginalIntegerAffineModel318.contacts p

end OriginalIntegerReciprocalOrderOverlap318
