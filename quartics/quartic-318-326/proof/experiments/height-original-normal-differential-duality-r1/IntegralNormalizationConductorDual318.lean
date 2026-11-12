module
public import IntegralNormalizationRawEmbedding318
public import OverorderMultiplierHom318
public import FiniteFrameFunctionalAdjunction318
public section
noncomputable section
namespace IntegralNormalizationConductorDual318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "A" => Source R a d
local notation "B" => OpenOrder R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "J" => IntegralFourRootNormalizationConductor318.conductor R a d

/-- Entire finite dual of the actual normalization chart, with its
literal raw-order coefficient formula, not just a rank comparison. -/
structure Data where
  equivalence : J ≃ (N →ₗ[P] P)
  value : ∀ (z : J) (n : N),∃ v : A,
    IntegralFourRootNormalizationConductor318.inclusion R a d v=z.val*n.val ∧
    equivalence z n=FourRootIntegralDuality318.coefficient
      (DistinctContactIntegralDomain318.coefficient R a d) v

/-- The actual denominator and raw perfect pairing construct every
functional. No projectivity/freeness of the normalization is assumed. -/
@[expose] def data : Data R a d := by
  let inc := IntegralFourRootNormalizationConductor318.inclusion R a d
  let into := IntegralFourRootNormalizationConductor318.intoNormal R a d
  letI : Algebra A B := inc.toAlgebra
  letI : Algebra A N := into.toAlgebra
  letI : IsScalarTower P A N := IsScalarTower.of_algebraMap_eq
    (fun p => (into.commutes p).symm)
  let j : N →ₐ[A] B :=
    { toRingHom := N.val.toRingHom
      commutes' := fun _ => rfl }
  have hj : Function.Injective j := Subtype.val_injective
  have hi : Function.Injective (algebraMap A B) :=
    IntegralNormalizationRawEmbedding318.inclusion_injective R a d hd
  obtain ⟨u,hu,huN⟩ := IntegralNormalizationRawEmbedding318.exists_denominator R a d hd
  let ec : J ≃ OverorderMultiplierHom318.Multipliers j :=
    { toFun := fun z => ⟨z.val,(FiniteOrderConductorTraceDual318.mem_conductor inc N z.val).mp z.property⟩
      invFun := fun z => ⟨z.val,(FiniteOrderConductorTraceDual318.mem_conductor inc N z.val).mpr z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eh := OverorderMultiplierHom318.equivalence j hi hj u hu huN
  let ef := FiniteFrameFunctionalAdjunction318.equivalence (N:=N)
    (FourRootIntegralDuality318.frame (DistinctContactIntegralDomain318.coefficient R a d))
  refine ⟨ec.trans (eh.trans ef),?_⟩
  intro z n
  refine ⟨OverorderMultiplierHom318.preimage j (ec z) n,?_,?_⟩
  · exact OverorderMultiplierHom318.preimage_spec j (ec z) n
  · exact FiniteFrameFunctionalAdjunction318.evaluate
      (FourRootIntegralDuality318.frame (DistinctContactIntegralDomain318.coefficient R a d))
      (eh (ec z)) n
end IntegralNormalizationConductorDual318
