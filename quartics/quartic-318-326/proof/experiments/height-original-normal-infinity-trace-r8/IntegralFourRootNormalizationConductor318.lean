module
public import FiniteOrderConductorTraceDual318
public import FourRootTraceDualLattice318
public import IntegralDistinctContactOpen318
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public section
noncomputable section
namespace IntegralFourRootNormalizationConductor318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "A" => Source R a d
local notation "B" => OpenOrder R a d

/-- Literal original order map with all four marked roots unchanged. -/
abbrev inclusion : A →ₐ[P] B :=
  FourRootSignBaseChange318.coefficientMap (DistinctContactIntegralDomain318.coefficient R a d) F
/-- The SAME integral closure used by the actual finite normalization
chart, before any field-valued specialization. -/
abbrev normalOrder : Subalgebra P B := integralClosure P B

lemma inclusion_mem (x : A) : inclusion R a d x ∈ normalOrder R a d := by
  letI : Module.Finite P A := (FourRootOrder318.finite_free _).1
  change IsIntegral P (inclusion R a d x)
  exact (IsIntegral.of_finite P x).map (inclusion R a d)

@[expose] def intoNormal : A →ₐ[P] normalOrder R a d :=
  (inclusion R a d).codRestrict (normalOrder R a d) (inclusion_mem R a d)
lemma intoNormal_value (x : A) : (intoNormal R a d x : B)=inclusion R a d x := rfl

@[expose] def different : B :=
  (16 : F) • FourRootTraceCoefficient318.rootProduct
    (fun i => algebraMap P F (DistinctContactIntegralDomain318.coefficient R a d i))

/-- The old whole-order trace-codifferent criterion is applied literally
with its genuine coefficient-change map and 16-times-marked-root product. -/
lemma raw_codifferent (z : B) :
    z ∈ FiniteTraceDualLattice318.lattice (K:=F) (inclusion R a d) ↔
      different R a d*z ∈ FiniteOrderConductorTraceDual318.orderImage (inclusion R a d) :=
  FourRootTraceDualLattice318.mem_iff_different_multiple
    (DistinctContactIntegralDomain318.coefficient R a d) z

@[expose] def conductor : Submodule P B :=
  FiniteOrderConductorTraceDual318.conductor (inclusion R a d) (normalOrder R a d)
@[expose] def codifferent : Submodule P B :=
  FiniteOrderConductorTraceDual318.traceDual (K:=F) (normalOrder R a d)

/-- Exact normalization correction: the full NORMAL-order trace
codifferent is the raw inverse-different times the ACTUAL conductor.
There is no conductor equality or smoothness premise. -/
theorem mem_codifferent_iff (z : B) :
    z ∈ codifferent R a d ↔ different R a d*z ∈ conductor R a d :=
  FiniteOrderConductorTraceDual318.traceDual_iff_conductor (inclusion R a d)
    (normalOrder R a d) (inclusion_mem R a d) (different R a d) (raw_codifferent R a d) z

lemma different_isUnit : IsUnit (different R a d) :=
  FourRootTraceDualLattice318.different_isUnit
    (DistinctContactIntegralDomain318.coefficient R a d)
    (two_unit R a d) (coefficient_unit R a d)

/-- Inverse form inside the SAME localized original algebra. Inverting
2 here is confined to the generic SOURCE OPEN, not the integral normal order. -/
theorem mem_codifferent_iff_inverse (z : B) : z ∈ codifferent R a d ↔
    ∃ x : B,x ∈ conductor R a d ∧ z=↑((different_isUnit R a d).unit⁻¹)*x := by
  rw [mem_codifferent_iff]
  constructor
  · intro hz
    refine ⟨different R a d*z,hz,?_⟩
    rw [←(different_isUnit R a d).unit_spec,←mul_assoc,Units.inv_mul,one_mul]
  · rintro ⟨x,hx,rfl⟩
    simpa only [←(different_isUnit R a d).unit_spec,←mul_assoc,Units.mul_inv,one_mul] using hx

lemma conductor_le_normal : conductor R a d ≤ (normalOrder R a d).toSubmodule :=
  FiniteOrderConductorTraceDual318.conductor_le_normal (inclusion R a d)
    (normalOrder R a d) (inclusion_mem R a d)
end IntegralFourRootNormalizationConductor318
