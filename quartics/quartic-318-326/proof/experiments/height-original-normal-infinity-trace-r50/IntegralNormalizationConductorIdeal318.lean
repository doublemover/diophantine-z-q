module
public import IntegralNormalizationCounit318
public section
noncomputable section
namespace IntegralNormalizationConductorIdeal318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "P" => Polynomial R
local notation "A" => Source R a d
local notation "B" => OpenOrder R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "J" => IntegralFourRootNormalizationConductor318.conductor R a d
local notation "inc" => IntegralFourRootNormalizationConductor318.inclusion R a d
local notation "into" => IntegralFourRootNormalizationConductor318.intoNormal R a d

/-- The ACTUAL conductor pulled back to the original whole raw order.
It is an ideal of that ring, not a chosen principal approximation. -/
@[expose] def ideal : Ideal A where
  carrier := {x | inc x ∈ J}
  zero_mem' := by rw [map_zero]; exact J.zero_mem
  add_mem' hx hy := by rw [map_add]; exact J.add_mem hx hy
  smul_mem' a x hx := by
    change inc (a*x) ∈ J
    rw [map_mul,mul_comm]
    exact FiniteOrderConductorTraceDual318.conductor_stable inc N (into a) (inc x) hx

lemma mem_ideal (x : A) : x ∈ ideal R a d ↔
    ∀ n : N,∃ y : A,inc y=inc x*n.val :=
  FiniteOrderConductorTraceDual318.mem_conductor inc N (inc x)

variable [IsDomain R] [CharZero R] [IsNoetherianRing R] [IsIntegrallyClosed R[X]]
  [IsDomain B] (hd : ∀ i,d i ≠ 0)

include hd in
/-- Exact image of the WHOLE normalization counit in the raw dual
frame. Every conductor element occurs and no other coefficient occurs. -/
theorem range_coordinate :
    letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
    LinearMap.range (IntegralNormalizationCounit318.coordinate R a d)=ideal R a d := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  let E := IntegralNormalizationFiniteDual318.equivalence R a d hd
  ext x
  constructor
  · rintro ⟨f,rfl⟩
    change inc (IntegralNormalizationCounit318.coordinate R a d f) ∈ J
    have he := IntegralNormalizationCounit318.coefficient_formula R a d hd (E.symm f)
    rw [LinearEquiv.apply_symm_apply] at he
    rw [he]
    exact (IntegralFourRootNormalizationConductor318.mem_codifferent_iff R a d _).mp
      (E.symm f).property
  · intro hx
    let cJ : J := ⟨inc x,hx⟩
    let z := (IntegralNormalizationTraceFunctional318.differentEquiv R a d).symm cJ
    refine ⟨E z,?_⟩
    apply IntegralNormalizationRawEmbedding318.inclusion_injective R a d hd
    have hz := congrArg Subtype.val
      ((IntegralNormalizationTraceFunctional318.differentEquiv R a d).apply_symm_apply cJ)
    exact (IntegralNormalizationCounit318.coefficient_formula R a d hd z).trans hz
end IntegralNormalizationConductorIdeal318
