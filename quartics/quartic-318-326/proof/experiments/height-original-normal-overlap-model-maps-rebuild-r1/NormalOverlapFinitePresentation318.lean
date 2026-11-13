module
public import IntegralNormalizationConductorDenominator318
public import IntegralInfinityNormalConductor318
public import Mathlib.Algebra.Module.FinitePresentation
public section
noncomputable section
namespace NormalOverlapFinitePresentation318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d

include hd in
lemma finite_order : Module.Finite P N := by
  letI : Module.Finite F B := (finite_free_etale R a d).1
  letI : Algebra.Etale F B := (finite_free_etale R a d).2.2
  exact (LocalizedNormalModel318.finite_normal_model (Rf:=F) (B:=B)
    (IntegralNormalizationConductorDenominator318.denominator R a d)
    (IntegralReciprocalBase318.finiteDenominator_ne_zero R a _
      (arithmeticDenominator_ne_zero R d hd))).1

include hd in
lemma finite_presentation : Module.FinitePresentation P N := by
  letI : Module.Finite P N := finite_order R a d hd
  exact Module.finitePresentation_of_finite P N

section Infinity
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local notation "Ni" => IntegralInfinityNormalConductor318.normalOrder R a d

include hd in
/-- No freeness is asserted: finite presentation is produced from actual
finite normalization over the Noetherian reciprocal polynomial base. -/
lemma infinity_presentation : Module.FinitePresentation P Ni := by
  letI : Module.Finite P Ni := IntegralInfinityNormalConductor318.finite_normal R a d hd
  exact Module.finitePresentation_of_finite P Ni
end Infinity
end NormalOverlapFinitePresentation318
