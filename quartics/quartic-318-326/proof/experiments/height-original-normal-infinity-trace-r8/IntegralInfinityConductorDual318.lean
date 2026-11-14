module
public import IntegralInfinityNormalConductor318
public import OverorderMultiplierHom318
public import FiniteFrameFunctionalAdjunction318
public section
noncomputable section
namespace IntegralInfinityConductorDual318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "A" => DVRNormalizedInfinityOrder318.Order R d a
local notation "B" => OpenOrder R a d
local instance : Algebra P F := IntegralInfinityReciprocalScalar318.baseAlgebra R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : IsScalarTower P F B := IntegralInfinityReciprocalScalar318.tower R a d
local notation "N" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "J" => IntegralInfinityNormalConductor318.conductor R a d

/-- Entire finite dual of the actual reciprocal normalization chart, with its
literal raw-order coefficient formula, not just a rank comparison. -/
structure Data where
  equivalence : J ≃ (N →ₗ[P] P)
  value : ∀ (z : J) (n : N),∃ v : A,
    IntegralInfinityRawEmbedding318.rawMap R a d v=z.val*n.val ∧
    equivalence z n=FourRootIntegralDuality318.coefficient
      (DVRNormalizedInfinityOrder318.coefficient R d a) v

/-- The actual reciprocal denominator and raw perfect pairing construct every
functional. No projectivity/freeness of the normalization is assumed. -/
@[expose] def data : Data R a d := by
  let inc := IntegralInfinityRawEmbedding318.rawMap R a d
  let into := IntegralInfinityNormalConductor318.intoNormal R a d
  letI : Algebra A B := inc.toAlgebra
  letI : Algebra A N := into.toAlgebra
  letI : IsScalarTower P A N := IsScalarTower.of_algebraMap_eq
    (fun p => (into.commutes p).symm)
  let j : N →ₐ[A] B :=
    { toRingHom := N.val.toRingHom
      commutes' := fun _ => rfl }
  have hj : Function.Injective j := Subtype.val_injective
  have hi : Function.Injective (algebraMap A B) :=
    IntegralInfinityRawEmbedding318.injective R a d hd
  obtain ⟨u,hu,huN⟩ := IntegralInfinityNormalConductor318.exists_denominator R a d hd
  let ec : J ≃ OverorderMultiplierHom318.Multipliers j :=
    { toFun := fun z => ⟨z.val,(FiniteOrderConductorTraceDual318.mem_conductor inc N z.val).mp z.property⟩
      invFun := fun z => ⟨z.val,(FiniteOrderConductorTraceDual318.mem_conductor inc N z.val).mpr z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eh := OverorderMultiplierHom318.equivalence j hi hj u hu huN
  let ef := FiniteFrameFunctionalAdjunction318.equivalence (N:=N)
    (FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient R d a))
  refine ⟨ec.trans (eh.trans ef),?_⟩
  intro z n
  refine ⟨OverorderMultiplierHom318.preimage j (ec z) n,?_,?_⟩
  · exact OverorderMultiplierHom318.preimage_spec j (ec z) n
  · exact FiniteFrameFunctionalAdjunction318.evaluate
      (FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient R d a))
      (eh (ec z)) n
end IntegralInfinityConductorDual318
