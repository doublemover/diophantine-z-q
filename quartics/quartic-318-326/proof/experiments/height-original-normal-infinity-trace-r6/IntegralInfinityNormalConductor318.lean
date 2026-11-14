module
public import IntegralInfinityRawEmbedding318
public section
noncomputable section
namespace IntegralInfinityNormalConductor318
open Polynomial IntegralDistinctContactOpen318 IntegralInfinitySourceParameters318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local notation "A" => DVRNormalizedInfinityOrder318.Order R d a
local instance : Algebra P F := IntegralInfinityReciprocalScalar318.baseAlgebra R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : IsScalarTower P F B := IntegralInfinityReciprocalScalar318.tower R a d
abbrev normalOrder : Subalgebra P B := integralClosure P B
local notation "N" => normalOrder R a d
local notation "inc" => IntegralInfinityRawEmbedding318.rawMap R a d
@[expose] def conductor : Submodule P B := FiniteOrderConductorTraceDual318.conductor inc N
@[expose] def codifferent : Submodule P B := FiniteOrderConductorTraceDual318.traceDual (K:=F) N
@[expose] def different : B := CoefficientPairingTrace318.euler (IntegralInfinityRawEmbedding318.frame R a d)

lemma raw_mem (x : A) : inc x ∈ N := by
  letI : Module.Finite P A := (DVRNormalizedInfinityOrder318.finite_free R d a).1
  exact (IsIntegral.of_finite P x).map inc
@[expose] def intoNormal : A →ₐ[P] N := inc.codRestrict N (raw_mem R a d)

lemma raw_codifferent (z : B) : z ∈ FiniteTraceDualLattice318.lattice (K:=F) inc ↔
    different R a d*z ∈ FiniteOrderConductorTraceDual318.orderImage inc :=
  FiniteTraceDualLattice318.mem_iff_euler_multiple
    (FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient R d a))
    (IntegralInfinityRawEmbedding318.frame R a d) inc
    (IntegralInfinityRawEmbedding318.basis R a d) (IntegralInfinityRawEmbedding318.coefficient R a d) z

/-- Full normal infinity trace lattice equals the inverse raw different
times the ACTUAL conductor, testing every normal-order element. -/
theorem mem_codifferent_iff (z : B) : z ∈ codifferent R a d ↔
    different R a d*z ∈ conductor R a d :=
  FiniteOrderConductorTraceDual318.traceDual_iff_conductor inc N (raw_mem R a d)
    (different R a d) (raw_codifferent R a d) z

lemma different_isUnit : IsUnit (different R a d) := by
  have hu (i : Fin 4) : IsUnit (infinityParameter R a d i) := by
    rw [parameter_identity]
    exact (coefficient_unit R a d i).mul ((parameterUnit R a d)⁻¹.isUnit.pow 2)
  have hd := FourRootTraceDualLattice318.different_isUnit
    (DVRNormalizedInfinityOrder318.coefficient R d a) (two_unit R a d) hu
  change IsUnit (CoefficientPairingTrace318.euler
    (PerfectCoefficientFrameTransport318.frame _ (sourceEquiv R a d)))
  rw [PerfectCoefficientFrameTransport318.euler,FourRootTraceCoefficient318.actual_euler]
  exact hd.map (sourceEquiv R a d).toRingHom

/-- Exact raw-different transition on the same source: all four
signed roots are divided by t, so the factor is t inverse to the fourth. -/
theorem different_transition : different R a d=
    (↑(parameterUnit R a d)⁻¹:F)^4 • IntegralFourRootNormalizationConductor318.different R a d := by
  have hp : sourceEquiv R a d (FourRootTraceCoefficient318.rootProduct (infinityParameter R a d))=
      (↑(parameterUnit R a d)⁻¹:F)^4 •
        FourRootTraceCoefficient318.rootProduct (finiteParameter R a d) := by
    rw [FourRootTraceCoefficient318.rootProduct_eq,map_prod,FourRootTraceCoefficient318.rootProduct_eq]
    simp_rw [sourceEquiv_root,Algebra.smul_def]
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,map_pow]
  change CoefficientPairingTrace318.euler
    (PerfectCoefficientFrameTransport318.frame _ (sourceEquiv R a d))=
      (↑(parameterUnit R a d)⁻¹:F)^4 •
        ((16:F) • FourRootTraceCoefficient318.rootProduct (finiteParameter R a d))
  rw [PerfectCoefficientFrameTransport318.euler,FourRootTraceCoefficient318.actual_euler,map_smul,hp]
  exact smul_comm _ _ _

lemma conductor_le_normal : conductor R a d ≤ N.toSubmodule :=
  FiniteOrderConductorTraceDual318.conductor_le_normal inc N (raw_mem R a d)

variable [IsDomain R] [CharZero R] [IsNoetherianRing R] [IsIntegrallyClosed P]
  [IsDomain B] (hd : ∀ i,d i ≠ 0)
include hd in
lemma finite_normal : Module.Finite P N := by
  letI : Module.Finite F B := (finite_free_etale R a d).1
  letI : Algebra.Etale F B := (finite_free_etale R a d).2.2
  exact (IntegralReciprocalNormalClosures318.reciprocal_normal_closure R a
    (arithmeticDenominator R d) B (arithmeticDenominator_ne_zero R d hd)).1

include hd in
/-- One actual reciprocal localization denominator clears EVERY element
of the whole normal infinity order, with its image a source unit. -/
lemma exists_denominator : ∃ u : A,IsUnit (inc u) ∧
    ∀ n : N,∃ v : A,inc v=inc u*n.val := by
  let s := IntegralReciprocalBase318.reciprocalDenominator R a (arithmeticDenominator R d)
  letI := IntegralInfinityReciprocalScalar318.localization R a d
  letI : Module.Finite P N := finite_normal R a d hd
  obtain ⟨r,hr⟩ := FiniteFrameConductorDenominator318.exists_denominator (Submonoid.powers s) inc
    (FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient R d a)).basis
    (IntegralInfinityRawEmbedding318.frame R a d).basis (IntegralInfinityRawEmbedding318.basis R a d) N
  refine ⟨algebraMap P A r,?_,?_⟩
  · rw [AlgHom.commutes,IsScalarTower.algebraMap_apply P F B]
    exact (IsLocalization.map_units F r).map (algebraMap F B)
  · rw [AlgHom.commutes]
    exact (FiniteOrderConductorTraceDual318.mem_conductor inc N _).mp hr
end IntegralInfinityNormalConductor318
