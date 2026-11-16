module
public import PELArithmeticZeroSection318
public section
noncomputable section
namespace PELArithmeticInversion318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318 PELComplexPeriodSurface318
open PELPrincipalThreeCovering318 PELArithmeticComplexFamily318 PELArithmeticOriginalFibers318
open PELJointOrderEndomorphisms318 PELArithmeticOrderEndomorphisms318 PELArithmeticZeroSection318
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000

theorem negative_identity_linear (z : ComplexVectors) :
    leftLinear (representation ((-1:order):PELQuaternionAlgebra318.B)) z= -z := by
  change leftLinear (representation (-1)) z= -z
  rw [map_neg,map_one]
  funext i
  fin_cases i <;> simp [leftLinear,action,Matrix.one_apply]

theorem negative_identity_fiber (τ : HalfPlane) (p : Surface τ) :
    orderEnd representation order τ (-1) p= -p := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective (Periods τ) p
  rw [orderEnd_mk,negative_identity_linear,map_neg]

theorem negative_identity_joint (p : Total) : jointOrder (-1) p=(p.1,-p.2) := by
  change (p.1,fiberEquiv p.1 (orderEnd representation order p.1 (-1)
    ((fiberEquiv p.1).symm p.2)))=_
  rw [negative_identity_fiber,map_neg,AddEquiv.apply_symm_apply]

/-- Inversion is the SAME original order element −1, descended globally;
there is no independent choice of group law on each orbit fiber. -/
@[expose] def arithmeticNeg : ArithmeticTotal → ArithmeticTotal := arithmeticOrder (-1)

theorem arithmeticNeg_square (p : Total) :
    arithmeticNeg (totalQuotient p)=totalQuotient (p.1,-p.2) := by
  rw [arithmeticNeg,arithmeticOrder_square,negative_identity_joint]

theorem arithmeticNeg_involutive : Function.Involutive arithmeticNeg := by
  intro p
  obtain ⟨x,rfl⟩ := totalQuotient_surjective p
  rw [arithmeticNeg_square,arithmeticNeg_square,neg_neg]

theorem arithmeticNeg_over_base (p : ArithmeticTotal) :
    arithmeticProjection (arithmeticNeg p)=arithmeticProjection p :=
  arithmeticOrder_over_base (-1) p

theorem arithmeticNeg_zero (p : ArithmeticBase) :
    arithmeticNeg (arithmeticZero p)=arithmeticZero p := by
  obtain ⟨τ,rfl⟩ := baseQuotient_surjective p
  rw [arithmeticZero_square]
  change arithmeticNeg (totalQuotient (τ,0))=totalQuotient (τ,0)
  rw [arithmeticNeg_square,neg_zero]

local instance : ChartedSpace Ambient ArithmeticTotal := arithmeticTotalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω ArithmeticTotal := arithmeticTotal_manifold

theorem arithmeticNeg_holomorphic :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω arithmeticNeg :=
  arithmeticOrder_holomorphic (-1)

theorem original_fiber_neg (τ : HalfPlane) (p : Surface τ) :
    arithmeticNeg (originalFiberEquiv τ p).val=(originalFiberEquiv τ (-p)).val := by
  have h := congrArg Subtype.val (original_fiber_order τ (-1) p)
  simpa only [arithmeticNeg,fiberOrder,negative_identity_fiber] using h
end PELArithmeticInversion318
