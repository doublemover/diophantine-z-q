module
public import IntegralNormalizationConductorDual318
public section
noncomputable section
namespace IntegralNormalizationTraceFunctional318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "J" => IntegralFourRootNormalizationConductor318.conductor R a d
local notation "L" => IntegralFourRootNormalizationConductor318.codifferent R a d
local notation "δ" => IntegralFourRootNormalizationConductor318.different R a d

/-- Literal multiplication by the raw different identifies the actual
normal-order trace codifferent with the conductor. Inverses remain in the
original source algebra, not the integral normal-order scalar ring. -/
@[expose] def differentEquiv : L ≃ J where
  toFun z := ⟨δ*z.val,(IntegralFourRootNormalizationConductor318.mem_codifferent_iff R a d z.val).mp z.property⟩
  invFun z := ⟨↑((IntegralFourRootNormalizationConductor318.different_isUnit R a d).unit⁻¹)*z.val,
    (IntegralFourRootNormalizationConductor318.mem_codifferent_iff_inverse R a d _).mpr
      ⟨z.val,z.property,rfl⟩⟩
  left_inv z := by
    apply Subtype.ext
    change ↑((IntegralFourRootNormalizationConductor318.different_isUnit R a d).unit⁻¹)*(δ*z.val)=z.val
    rw [←(IntegralFourRootNormalizationConductor318.different_isUnit R a d).unit_spec,
      ←mul_assoc,Units.inv_mul,one_mul]
  right_inv z := by
    apply Subtype.ext
    change δ*(↑((IntegralFourRootNormalizationConductor318.different_isUnit R a d).unit⁻¹)*z.val)=z.val
    rw [←(IntegralFourRootNormalizationConductor318.different_isUnit R a d).unit_spec,
      ←mul_assoc,Units.mul_inv,one_mul]

/-- Every polynomial-linear functional on the ACTUAL normal order is
represented by one actual trace-codifferent coefficient. -/
@[expose] def equivalence : L ≃ (N →ₗ[P] P) :=
  (differentEquiv R a d).trans (IntegralNormalizationConductorDual318.data R a d hd).equivalence

/-- The functional is precisely the original algebra trace pairing.
The map includes the actual polynomial scalar injection into its open base. -/
theorem trace_value (z : L) (n : N) :
    algebraMap P F (equivalence R a d hd z n)=Algebra.trace F B (z.val*n.val) := by
  obtain ⟨v,hv,he⟩ := (IntegralNormalizationConductorDual318.data R a d hd).value
    (differentEquiv R a d z) n
  change IntegralFourRootNormalizationConductor318.inclusion R a d v=(δ*z.val)*n.val at hv
  change algebraMap P F
    ((IntegralNormalizationConductorDual318.data R a d hd).equivalence (differentEquiv R a d z) n)=_
  rw [he,FourRootTraceCoefficient318.trace_eq,←mul_assoc,←hv]
  exact (FourRootDualityBaseChange318.coefficientMap_coefficient
    (DistinctContactIntegralDomain318.coefficient R a d) v).symm

/-- No normal-order functional remains unrepresented; the coefficient
is unique in the SAME ambient original source algebra. -/
theorem existsUnique_coefficient (f : N →ₗ[P] P) :
    ∃! z : L,equivalence R a d hd z=f := by
  refine ⟨(equivalence R a d hd).symm f,(equivalence R a d hd).apply_symm_apply f,?_⟩
  intro z hz
  apply (equivalence R a d hd).injective
  exact hz.trans ((equivalence R a d hd).apply_symm_apply f).symm
end IntegralNormalizationTraceFunctional318
