module
public import PELNormOneDiscreteSLGroup318
public section
noncomputable section
namespace PELNormOneBaseAction318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicUnitPeriodTransport318
open PELJointArithmeticLift318 PELJointArithmeticCoherence318 PELJointNormOneAction318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open PELNormOneDiscreteSLGroup318 PELPrincipalBaseHolomorphy318 PELNormOneBaseStabilizer318
open PELPositiveOrderNormalizer318 PELNormalizerArithmeticBase318
open scoped Manifold ContDiff
set_option maxHeartbeats 1500000

instance : MulAction normOneUnits HalfPlane where
  smul u τ := nextParameter u.val u.property τ
  one_smul τ := congrArg Prod.fst (lift_one (τ,(0:ComplexVectors)))
  mul_smul u v τ := (congrArg Prod.fst
    (lift_mul u.val v.val u.property v.property (τ,(0:ComplexVectors)))).symm

theorem toUpper_equivariant (u : normOneUnits) (τ : HalfPlane) :
    PELPrincipalProperAction318.toUpper (u • τ)=
      intoImage u • PELPrincipalProperAction318.toUpper τ := by
  apply UpperHalfPlane.ext
  change unitParameter representation order u.val τ=
    ((specialLinear u • PELPrincipalProperAction318.toUpper τ:UpperHalfPlane):ℂ)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

instance base_proper : ProperlyDiscontinuousSMul normOneUnits HalfPlane :=
  PELPrincipalProperAction318.proper_of_equivariant intoImage intoImage_injective
    PELPrincipalProperAction318.toUpper PELPrincipalProperAction318.toUpper_continuous
    toUpper_equivariant

@[expose] def originalNormalizer (u : normOneUnits) : positiveNormalizer :=
  ⟨PELQuaternionNormParity318.integralUnit u.val,
    PELActualOrderNormalizer318.integral_mem u.val,by
      change 0<PELQuaternionAlgebra318.reducedNorm ((u.val:order):PELQuaternionAlgebra318.B)
      rw [(mem_normOneUnits u.val).mp u.property]
      norm_num⟩

theorem normalizer_action (u : normOneUnits) (τ : HalfPlane) :
    PELPositiveNormalizerMobius318.baseAction (originalNormalizer u) τ=u • τ := rfl

local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold

theorem base_holomorphic (u : normOneUnits) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun τ : HalfPlane => u • τ) :=
  baseAction_holomorphic (originalNormalizer u)

instance base_continuous : ContinuousConstSMul normOneUnits HalfPlane where
  continuous_const_smul u := (base_holomorphic u).continuous

/-- The scalar signs act trivially on the original base coordinate. They
do NOT act trivially on every point of the original surface family. -/
theorem sign_parameter (u : orderˣ) (hu : u=1 ∨ u= -1) (τ : ℂ) :
    unitParameter representation order u τ=τ := by
  rcases hu with rfl | rfl
  · change QuaternionicMobiusPeriods318.mobius (representation 1) τ=τ
    rw [map_one]
    simp [QuaternionicMobiusPeriods318.mobius,QuaternionicMobiusPeriods318.denominator,
      Matrix.one_apply]
  · change QuaternionicMobiusPeriods318.mobius (representation (-1)) τ=τ
    rw [map_neg,map_one]
    simp [QuaternionicMobiusPeriods318.mobius,QuaternionicMobiusPeriods318.denominator,
      Matrix.one_apply]

theorem stabilizer_sign (u : normOneUnits) (τ : HalfPlane) (h : u • τ=τ) :
    u.val=1 ∨ u.val= -1 :=
  fixed_implies_sign u.val ((mem_normOneUnits u.val).mp u.property) τ τ.property
    (congrArg Subtype.val h)
end PELNormOneBaseAction318
