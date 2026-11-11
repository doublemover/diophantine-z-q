module
public import PELOriginalOrderAutomorphisms318
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Analysis.Normed.Module.Connected
public section
noncomputable section
namespace PELOriginalOrderActionFaithful318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open QuaternionicOrderPeriodQuotient318 QuaternionicOrderQuotientActionLaws318
open PELOriginalOrderSchemeMorphism318 PELOriginalSchemePointGroup318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance periodsDiscrete : DiscreteTopology (periodSubgroup representation order τ) :=
  PELOriginalPeriodLattice318.original_discrete τ hτ

/-- A continuous complex-linear map whose entire image lies in the
actual discrete original period lattice is zero. The connected source
and discrete target are used, not a false torsion-free quotient premise. -/
lemma linear_into_periods_zero (F : ComplexVectors →ₗ[ℂ] ComplexVectors)
    (hF : ∀ z, F z ∈ periodSubgroup representation order τ) : ∀ z,F z=0 := by
  let g : ComplexVectors → periodSubgroup representation order τ := fun z => ⟨F z,hF z⟩
  have hg : Continuous g := F.toContinuousLinearMap.continuous.subtype_mk _
  intro z
  have he : g z=g 0 := TotallyDisconnectedSpace.eq_of_continuous g hg z 0
  have hv := congrArg Subtype.val he
  simpa only [g,map_zero] using hv

/-- Faithfulness uses the original discrete lattice and the faithful
original quaternion splitting, not a chosen abstract group action. -/
theorem zero_of_action_zero (a : order)
    (ha : ∀ q,orderEnd representation order τ a q=0) : a=0 := by
  have hl : ∀ z, leftLinear (representation a) z ∈ periodSubgroup representation order τ := by
    intro z
    apply (QuotientAddGroup.eq_zero_iff _).mp
    have he := ha (QuotientAddGroup.mk' (periodSubgroup representation order τ) z)
    change QuotientAddGroup.mk' (periodSubgroup representation order τ)
      (leftLinear (representation a) z)=0 at he
    exact he
  have hz := linear_into_periods_zero τ hτ (leftLinear (representation a)) hl
  have hm : representation (a : PELQuaternionAlgebra318.B)=0 := by
    ext i j
    fin_cases j
    · have hc := congrFun (hz ![1,0]) i
      have hc' : (representation a i 0 : ℂ)=0 := by simpa [leftLinear,action] using hc
      exact_mod_cast hc'
    · have hc := congrFun (hz ![0,1]) i
      have hc' : (representation a i 1 : ℂ)=0 := by simpa [leftLinear,action] using hc
      exact_mod_cast hc'
  apply Subtype.ext
  apply representation_injective
  simpa only [map_zero] using hm

theorem original_action_injective : Function.Injective (orderEnd representation order τ) := by
  intro a b hab
  have he : ringAction representation order τ (a-b)=0 := by
    rw [map_sub]
    change orderEnd representation order τ a-orderEnd representation order τ b=0
    rw [hab,sub_self]
  have hz : a-b=0 := zero_of_action_zero τ hτ (a-b) (fun q =>
    congrArg (fun f : AddMonoid.End (PeriodQuotient representation order τ) => f q) he)
  exact sub_eq_zero.mp hz

/-- The algebraized maps embed the ENTIRE original order faithfully in
actual candidate scheme endomorphisms. -/
theorem scheme_action_injective : Function.Injective (morphism τ hτ) := by
  intro a b hab
  apply original_action_injective τ hτ
  apply AddMonoidHom.ext
  intro q
  apply PELOriginalChartSchemePointIdentity318.candidate_point_injective τ hτ
  rw [←point_action τ hτ a q,←point_action τ hτ b q,hab]

/-- Faithfulness already holds on genuine complex points of the
represented group, with its exact original theta identification. -/
theorem complex_ring_action_injective : Function.Injective
    (PELOriginalUniversalOrderAction318.ringAction τ hτ (𝟙 (Spec (CommRingCat.of ℂ)))) := by
  intro a b hab
  apply original_action_injective τ hτ
  apply AddMonoidHom.ext
  intro q
  apply (PELOriginalTorusPointAddEquiv318.originalAddEquiv τ hτ).injective
  rw [←PELOriginalOrderAutomorphisms318.original_equiv_action τ hτ a q,
    ←PELOriginalOrderAutomorphisms318.original_equiv_action τ hτ b q]
  exact congrArg (fun f : AddMonoid.End (Points τ hτ (Spec (CommRingCat.of ℂ)) (𝟙 _)) =>
    f (PELOriginalTorusPointAddEquiv318.originalAddEquiv τ hτ q)) hab
end PELOriginalOrderActionFaithful318
