module
public import IntegralNormalizationCounit318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace IntegralNormalizationFiniteMap318
open AlgebraicGeometry CategoryTheory Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "A" => Source R a d
local notation "B" => OpenOrder R a d
local notation "F" => Base R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "into" => IntegralFourRootNormalizationConductor318.intoNormal R a d

/-- Literal finite-chart normalization morphism to the raw order. -/
@[expose] def map : Spec (CommRingCat.of N) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom into.toRingHom)

include hd in
/-- Finiteness is produced from the actual original arithmetic open
and integral closure, then restricted through the literal raw order. -/
theorem finite : IsFinite (map R a d) := by
  letI : Module.Finite F B := (finite_free_etale R a d).1
  letI : Algebra.Etale F B := (finite_free_etale R a d).2.2
  let s := IntegralNormalizationConductorDenominator318.denominator R a d
  have hs : s ≠ 0 := IntegralReciprocalBase318.finiteDenominator_ne_zero R a _
    (arithmeticDenominator_ne_zero R d hd)
  letI : Module.Finite P N := (LocalizedNormalModel318.finite_normal_model (Rf:=F) (B:=B) s hs).1
  letI : Algebra A N := into.toAlgebra
  letI : IsScalarTower P A N := IsScalarTower.of_algebraMap_eq
    (fun r => (into.commutes r).symm)
  letI : Module.Finite A N := Module.Finite.of_restrictScalars_finite P A N
  exact IsFinite.SpecMap_iff.mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The finite map agrees with the SAME raw embedding on the original
source open, as an equality of actual scheme morphisms. -/
theorem source_square :
    Spec.map (CommRingCat.ofHom N.val.toRingHom) ≫ map R a d=
      Spec.map (CommRingCat.ofHom
        (IntegralFourRootNormalizationConductor318.inclusion R a d).toRingHom) := by
  rw [map,←Spec.map_comp]
  rfl
end IntegralNormalizationFiniteMap318
