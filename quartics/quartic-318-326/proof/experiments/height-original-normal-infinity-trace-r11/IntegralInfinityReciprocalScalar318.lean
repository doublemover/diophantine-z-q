module
public import IntegralReciprocalNormalClosures318
public import IntegralDistinctContactOpen318
public section
noncomputable section
namespace IntegralInfinityReciprocalScalar318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local notation "δ" => arithmeticDenominator R d
local notation "G" => IntegralReciprocalBase318.ReciprocalBase R a δ

@[expose] def baseMap : P →+* F :=
  (IntegralReciprocalBase318.backward R a δ).comp (algebraMap P G)
@[expose] def sourceMap : P →+* B := (algebraMap F B).comp (baseMap R a d)

lemma baseMap_value (p : P) : baseMap R a d p=
    IntegralReciprocalBase318.reciprocalPolynomial R a δ p :=
  IntegralReciprocalBase318.backward_map R a δ p
lemma sourceMap_original : sourceMap R a d=
    IntegralReciprocalNormalClosures318.reciprocalPolynomialMap R a δ B := rfl

/-- Explicit reciprocal actions on the SAME source/base carriers. -/
@[instance_reducible] def baseAlgebra : Algebra P F := (baseMap R a d).toAlgebra
@[instance_reducible] def sourceAlgebra : Algebra P B := (sourceMap R a d).toAlgebra

local instance : Algebra P F := baseAlgebra R a d
local instance : Algebra P B := sourceAlgebra R a d

@[expose] def baseEquiv : G ≃ₐ[P] F :=
  { (IntegralReciprocalBase318.reciprocalEquiv R a δ).symm with
    commutes' := fun _ => rfl }

/-- The source base is an actual localization of the reciprocal
polynomial ring, with its reciprocal action, not its canonical action. -/
lemma localization : IsLocalization.Away (IntegralReciprocalBase318.reciprocalDenominator R a δ) F :=
  IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (IntegralReciprocalBase318.reciprocalDenominator R a δ)) (baseEquiv R a d)

@[instance_reducible] def tower : IsScalarTower P F B :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
end IntegralInfinityReciprocalScalar318
