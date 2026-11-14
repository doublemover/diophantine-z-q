module
public import IntegralInfinityConductorDual318
public section
noncomputable section
namespace IntegralInfinityTraceFunctional318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local instance : Algebra P F := IntegralInfinityReciprocalScalar318.baseAlgebra R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : IsScalarTower P F B := IntegralInfinityReciprocalScalar318.tower R a d
local notation "N" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "J" => IntegralInfinityNormalConductor318.conductor R a d
local notation "L" => IntegralInfinityNormalConductor318.codifferent R a d
local notation "δ" => IntegralInfinityNormalConductor318.different R a d
local notation "u" => (IntegralInfinityNormalConductor318.different_isUnit R a d).unit

@[expose] def differentEquiv : L ≃ J where
  toFun z := ⟨δ*z.val,(IntegralInfinityNormalConductor318.mem_codifferent_iff R a d z.val).mp z.property⟩
  invFun z := ⟨(↑u⁻¹:B)*z.val,by
    rw [IntegralInfinityNormalConductor318.mem_codifferent_iff,
      ←(IntegralInfinityNormalConductor318.different_isUnit R a d).unit_spec,
      ←mul_assoc,Units.mul_inv,one_mul]
    exact z.property⟩
  left_inv z := by
    apply Subtype.ext
    change (↑u⁻¹:B)*(δ*z.val)=z.val
    rw [←(IntegralInfinityNormalConductor318.different_isUnit R a d).unit_spec,
      ←mul_assoc,Units.inv_mul,one_mul]
  right_inv z := by
    apply Subtype.ext
    change δ*((↑u⁻¹:B)*z.val)=z.val
    rw [←(IntegralInfinityNormalConductor318.different_isUnit R a d).unit_spec,
      ←mul_assoc,Units.mul_inv,one_mul]

/-- Every polynomial functional on the WHOLE actual reciprocal normal
order is represented by an actual trace-integral source coefficient. -/
@[expose] def equivalence : L ≃ (N →ₗ[P] P) :=
  (differentEquiv R a d).trans (IntegralInfinityConductorDual318.data R a d hd).equivalence

/-- Literal algebra trace over the reciprocal scalar base, not an
unidentified perfect pairing with an omitted normalization scalar. -/
theorem trace_value (z : L) (n : N) :
    algebraMap P F (equivalence R a d hd z n)=Algebra.trace F B (z.val*n.val) := by
  obtain ⟨v,hv,he⟩ := (IntegralInfinityConductorDual318.data R a d hd).value
    (differentEquiv R a d z) n
  change IntegralInfinityRawEmbedding318.rawMap R a d v=(δ*z.val)*n.val at hv
  change algebraMap P F
    ((IntegralInfinityConductorDual318.data R a d hd).equivalence (differentEquiv R a d z) n)=_
  rw [he,CoefficientPairingTrace318.trace_eq (IntegralInfinityRawEmbedding318.frame R a d)]
  change _=(IntegralInfinityRawEmbedding318.frame R a d).coefficient (δ*(z.val*n.val))
  rw [←mul_assoc,←hv]
  exact (IntegralInfinityRawEmbedding318.coefficient R a d v).symm
end IntegralInfinityTraceFunctional318
