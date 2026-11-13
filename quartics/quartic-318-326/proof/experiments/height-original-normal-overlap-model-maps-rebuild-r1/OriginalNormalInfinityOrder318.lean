module
public import IntegralClosureAlongRingMap318
public import OriginalNormalDualDifferential318
public section
noncomputable section
namespace OriginalNormalInfinityOrder318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open IntegralDistinctContactOpen318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "F" => Base R a d
local notation "δ" => arithmeticDenominator R d

@[expose] def polynomialMap : P →+* B :=
  IntegralReciprocalNormalClosures318.reciprocalPolynomialMap R a δ B

abbrev Order := IntegralClosureAlongRingMap318.Closure (polynomialMap c t w D)
abbrev polynomialScalar : P →+* Order c t w D :=
  IntegralClosureAlongRingMap318.scalar (polynomialMap c t w D)
abbrev inclusion : Order c t w D →+* B :=
  IntegralClosureAlongRingMap318.inclusion (polynomialMap c t w D)
@[expose] def scalar : R →+* Order c t w D := (polynomialScalar c t w D).comp C

lemma polynomial_square : (inclusion c t w D).comp (polynomialScalar c t w D)=
    polynomialMap c t w D := IntegralClosureAlongRingMap318.square _

lemma polynomial_X : polynomialMap c t w D X=
    (↑(IntegralNormalReciprocalForms318.coordinateUnit R a d)⁻¹:B) :=
  IntegralNormalReciprocalForms318.reciprocal_polynomial R a d

lemma polynomial_C (r : R) : polynomialMap c t w D (C r)=algebraMap R B r := by
  change algebraMap F B (IntegralReciprocalBase318.backward R a δ
    (algebraMap P (IntegralReciprocalBase318.ReciprocalBase R a δ) (C r)))=_
  rw [IntegralReciprocalBase318.backward_map]
  change algebraMap F B (Polynomial.aeval
    (↑(IntegralReciprocalBase318.tUnit R a δ)⁻¹:F) (C r))=_
  rw [Polynomial.aeval_C,←IsScalarTower.algebraMap_apply R F B]

/-- Finiteness of the ENTIRE reciprocal normal order is produced from
the original etale arithmetic source, not assumed as a chart input. -/
lemma finite_polynomial : (polynomialScalar c t w D).Finite := by
  letI : IsDomain B := open_domain R a d (K c t) (IsFractionRing.injective R (K c t))
    (contacts_injective c t w) (coefficients_ne_zero c t w D)
  letI : Module.Finite F B := (finite_free_etale R a d).1
  letI : Algebra.Etale F B := (finite_free_etale R a d).2.2
  letI := (polynomialMap c t w D).toAlgebra
  letI : Module.Finite P (integralClosure P B) :=
    (IntegralReciprocalNormalClosures318.reciprocal_normal_closure R a δ B
      (arithmeticDenominator_ne_zero R d (coefficients_ne_zero c t w D))).1
  exact RingHom.finite_algebraMap.mpr inferInstance
end OriginalNormalInfinityOrder318
