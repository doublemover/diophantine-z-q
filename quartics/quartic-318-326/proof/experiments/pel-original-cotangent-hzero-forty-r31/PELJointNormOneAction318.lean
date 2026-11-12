module
public import PELJointArithmeticCoherence318
public import PELPeriodDeterminant318
public section
noncomputable section
namespace PELJointNormOneAction318
open QuaternionicRealPeriod318 QuaternionicUnitPeriodTransport318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318
open PELJointComplexAtlas318 PELJointArithmeticLift318 PELJointArithmeticCoherence318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open scoped Manifold ContDiff
set_option maxHeartbeats 1200000
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

/-- The arithmetic group consists of original ORDER units. The determinant
criterion below is identified with their original rational reduced norm. -/
@[expose] def normOneUnits : Subgroup orderˣ where
  carrier := {u | (unitMatrix representation order u).det=1}
  one_mem' := determinant_one
  mul_mem' := fun hu hv => determinant_mul _ _ hu hv
  inv_mem' := fun hu => determinant_inv _ hu

theorem mem_normOneUnits (u : orderˣ) :
    u∈normOneUnits ↔ reducedNorm ((u:order):B)=1 := by
  change (representation ((u:order):B)).det=1 ↔ _
  rw [PELPeriodDeterminant318.representation_det]
  norm_cast

/-- A genuine group action on the joint original complex family, with the
same original unit multiplication and holomorphic automorphisms. -/
instance : MulAction normOneUnits Total where
  smul u p := totalAction u.val u.property p
  one_smul p := total_one p
  mul_smul u v p := (total_mul u.val v.val u.property v.property p).symm

theorem action_holomorphic (u : normOneUnits) :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (fun p : Total => u • p) :=
  PELJointArithmeticHolomorphy318.totalAction_holomorphic u.val u.property

theorem action_projection_square (u : normOneUnits) (p : Cover) :
    u • familyProjection p=familyProjection (lift u.val u.property p) :=
  projection_square u.val u.property p

theorem action_base (u : normOneUnits) (p : Total) :
    (u • p).1=nextParameter u.val u.property p.1 := rfl

/-- On each original fiber the SAME principal form is preserved, while the
preceding theorem establishes that these changes are jointly holomorphic. -/
theorem original_polarization_preserved (u : normOneUnits) (τ : HalfPlane) (z w : ComplexVectors) :
    PELPeriodRiemannForm318.riemann (nextParameter u.val u.property τ)
      (nextParameter u.val u.property τ).property
      (scalarEquiv (unitDenominator representation order u.val τ)
        (PELOriginalUnitBiholomorph318.denominator_nonzero u.val u.property τ τ.property) z)
      (scalarEquiv (unitDenominator representation order u.val τ)
        (PELOriginalUnitBiholomorph318.denominator_nonzero u.val u.property τ τ.property) w)=
      PELPeriodRiemannForm318.riemann τ τ.property z w :=
  PELOriginalUnitBiholomorph318.riemann_transport u.val u.property τ τ.property z w
end PELJointNormOneAction318
