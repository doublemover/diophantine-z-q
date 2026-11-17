module
public import IntegerPolynomialFractionField318
public import OriginalIntegerFractionField318
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section
namespace OriginalIntegerFiniteClosure318
open Polynomial
attribute [local instance] IntegerPolynomialFractionField318.fieldAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev K := RatFunc ℚ
abbrev L := OriginalIntegerFractionField318.L c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- The original Kummer field with the parameter-preserving Z[T] algebra. -/
@[expose] def baseAlgebra : Algebra ℤ[X] (L c) :=
  ((algebraMap K (L c)).comp (algebraMap ℤ[X] K)).toAlgebra
attribute [local instance] baseAlgebra

local instance baseTower : IsScalarTower ℤ[X] K (L c) :=
  IsScalarTower.of_algebraMap_eq' (R := ℤ[X]) (S := K) (A := L c) rfl
local instance baseFraction : IsFractionRing ℤ[X] K :=
  IntegerPolynomialFractionField318.actual_fractionField

/-- Finite dimension is derived from the four explicit monic quadratic
factors. It is not a hypothesis about an unspecified field extension. -/
theorem extension_finite : Module.Finite K (L c) :=
  (FourRootOrder318.finite_free (SourceKummerField318.parameter c)).1

/-- The integral closure of the parameter ring in the actual original field.
Its gluing to a projective normalized model is a separate construction. -/
abbrev Closure := integralClosure ℤ[X] (L c)

/-- Finiteness uses the trace-lattice theorem over the normal Noetherian
ring Z[T]. It does not falsely treat Z[T] as a Dedekind or principal ring. -/
theorem closure_finite : Module.Finite ℤ[X] (Closure c) := by
  letI : Module.Finite K (L c) := extension_finite c
  exact IsIntegralClosure.finite ℤ[X] K (L c) (Closure c)

theorem closure_noetherian : IsNoetherianRing (Closure c) := by
  letI : Module.Finite K (L c) := extension_finite c
  exact IsIntegralClosure.isNoetherianRing ℤ[X] K (L c) (Closure c)

/-- The closure retains the same original function field. No smoothness or
regularity follows from this fraction-field statement. -/
theorem closure_fractionField : IsFractionRing (Closure c) (L c) := by
  letI : Module.Finite K (L c) := extension_finite c
  exact IsIntegralClosure.isFractionRing_of_finite_extension ℤ[X] K (L c) (Closure c)

/-- Normality of this affine integral closure is derived, not imposed on the
original monic order or on its possibly nonreduced special fibers. -/
theorem closure_normal : IsIntegrallyClosed (Closure c) := by
  letI : Module.Finite K (L c) := extension_finite c
  exact integralClosure.isIntegrallyClosedOfFiniteExtension (R := ℤ[X]) (L := L c) K

end OriginalIntegerFiniteClosure318
