module
public import OriginalIntegerNormalizationMap318
public import IntegralClosureAwayField318
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace OriginalIntegerNormalizedOverlap318
open Polynomial AlgebraicGeometry CategoryTheory
attribute [local instance] IntegerPolynomialFractionField318.fieldAlgebra
attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev L := OriginalIntegerFiniteClosure318.L c
abbrev Closure := OriginalIntegerFiniteClosure318.Closure c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- The actual parameter in the original field is nonzero. This follows
from the parameter-preserving Z[T] -> Q(T) -> L maps, not an assumption
about a chosen model. -/
theorem parameter_ne_zero : algebraMap ℤ[X] (L c) X ≠ 0 := by
  intro h
  letI : IsFractionRing ℤ[X] (RatFunc ℚ) :=
    IntegerPolynomialFractionField318.actual_fractionField
  apply Polynomial.X_ne_zero (R := ℤ)
  apply IsFractionRing.injective ℤ[X] (RatFunc ℚ)
  apply (algebraMap (RatFunc ℚ) (L c)).injective
  change algebraMap ℤ[X] (L c) X = algebraMap (RatFunc ℚ) (L c)
    (algebraMap ℤ[X] (RatFunc ℚ) 0)
  simpa only [map_zero] using h

@[expose] def parameterUnit : IsUnit (algebraMap ℤ[X] (L c) X) :=
  IsUnit.mk0 _ (parameter_ne_zero c)

/-- The normalized punctured chart inside the ORIGINAL field, with
Laurent coefficient action induced from the finite chart's exact map. -/
abbrev Overlap := IntegralClosureAwayField318.AwayClosure (X : ℤ[X]) (parameterUnit c)

@[expose] def inclusion : Closure c →ₐ[ℤ[X]] Overlap c :=
  IntegralClosureAwayField318.inclusion (X : ℤ[X]) (parameterUnit c)

@[expose] def overlapAlgebra : Algebra (Closure c) (Overlap c) :=
  IntegralClosureAwayField318.closureAlgebra (X : ℤ[X]) (parameterUnit c)
attribute [local instance] overlapAlgebra

theorem overlap_localization :
    IsLocalization.Away (algebraMap ℤ[X] (Closure c) X) (Overlap c) :=
  IntegralClosureAwayField318.localization (X : ℤ[X]) (parameterUnit c)

@[expose] def intoFinite : Spec (CommRingCat.of (Overlap c)) ⟶
    Spec (CommRingCat.of (Closure c)) :=
  Spec.map (CommRingCat.ofHom (inclusion c).toRingHom)

/-- This is an actual open immersion between the normalized affine charts,
not just an abstract isomorphism of unspecified fraction fields. -/
instance intoFinite_open : IsOpenImmersion (intoFinite c) := by
  letI := overlap_localization c
  exact IsOpenImmersion.of_isLocalization (algebraMap ℤ[X] (Closure c) X)

/-- Exact image of the original integer order in the normalized overlap. -/
@[expose] def orderToOverlap : OriginalIntegerAffineModel318.Order c →ₐ[ℤ[X]] Overlap c :=
  (inclusion c).comp (OriginalIntegerNormalizationMap318.toClosure c)

theorem orderToOverlap_val (z : OriginalIntegerAffineModel318.Order c) :
    (orderToOverlap c z).val = OriginalIntegerFractionField318.fieldEmbedding c z := rfl

theorem orderToOverlap_injective : Function.Injective (orderToOverlap c) :=
  (IntegralClosureAwayField318.inclusion_injective (X : ℤ[X]) (parameterUnit c)).comp
    (OriginalIntegerNormalizationMap318.toClosure_injective c)

end OriginalIntegerNormalizedOverlap318
