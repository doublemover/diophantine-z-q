module
public import QuaternionicIntegralPeriodMap318
public section
noncomputable section
namespace PELPositiveNormPeriodMap318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicMobiusPeriods318
open QuaternionicPositiveDeterminant318 QuaternionicIntegralPeriodMap318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELComplexPeriodSurface318 PELPeriodDeterminant318 DiscreteComplexPeriodEquiv318
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
variable (n : order) (hn : 0<reducedNorm (n:B)) (τ : ℂ) (hτ : 0<τ.im)

include hn in
theorem positive_determinant : 0<(representation n).det := by
  rw [representation_det]
  exact_mod_cast hn

@[expose] def translated : ℂ := parameter representation order n τ
include hn hτ in
theorem translated_positive : 0<(translated n τ).im :=
  mobius_positive_det _ (positive_determinant n hn) τ hτ
include hn hτ in
theorem scalar_nonzero : denominator (representation n) τ≠0 :=
  denominator_nonzero _ (positive_determinant n hn) τ hτ

/-- Genuine nonunit map in the correct direction: the translated original
surface maps ONTO the original surface. No inverse lattice equality is claimed. -/
@[expose] def originalMap : Surface (translated n τ) →+ Surface τ :=
  quotientMap representation order n τ (scalar_nonzero n hn τ hτ)

theorem originalMap_period (z : ComplexVectors) :
    originalMap n hn τ hτ (QuotientAddGroup.mk' (Periods (translated n τ)) z)=
      QuotientAddGroup.mk' (Periods τ) (periodScalar representation order n τ z) := rfl

theorem originalMap_surjective : Function.Surjective (originalMap n hn τ hτ) :=
  quotientMap_surjective representation order n τ (scalar_nonzero n hn τ hτ)

theorem originalMap_order (a : order) (p : Surface (translated n τ)) :
    originalMap n hn τ hτ (orderEnd representation order (translated n τ) a p)=
      orderEnd representation order τ a (originalMap n hn τ hτ p) :=
  quotientMap_order representation order n τ (scalar_nonzero n hn τ hτ) a p

local instance : DiscreteTopology (Periods τ) := PELOriginalPeriodLattice318.original_discrete τ hτ
local instance : DiscreteTopology (Periods (translated n τ)) :=
  PELOriginalPeriodLattice318.original_discrete _ (translated_positive n hn τ hτ)

/-- The actual nonunit map is holomorphic for BOTH original surface
atlases, using its exact scalar projection square on all vectors. -/
theorem originalMap_holomorphic :
    letI := surfaceCharts (translated n τ) (translated_positive n hn τ hτ)
    letI := surfaceCharts τ hτ
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (originalMap n hn τ hτ) :=
  descended_linear_between (Periods (translated n τ)) (Periods τ)
    (periodScalar representation order n τ) (originalMap n hn τ hτ)
    (originalMap_period n hn τ hτ)

/-- The original positive Riemann form pulls back with EXACT reduced-norm
multiplier. In particular this map is not called a fixed-polarization isomorphism. -/
theorem polarization_multiplier (z w : ComplexVectors) :
    PELPeriodRiemannForm318.riemann τ hτ
      (periodScalar representation order n τ z) (periodScalar representation order n τ w)=
    (reducedNorm (n:B):ℝ)*PELPeriodRiemannForm318.riemann (translated n τ)
      (translated_positive n hn τ hτ) z w := by
  let M := (periodEquiv (translated n τ) (translated_positive n hn τ hτ)).symm z
  let N := (periodEquiv (translated n τ) (translated_positive n hn τ hτ)).symm w
  have hperiod (L : RealMatrices) :
      period τ (L*representation n)=
        periodScalar representation order n τ (period (translated n τ) L) := by
    change period τ (L*representation n)=
      denominator (representation n) τ • period (mobius (representation n) τ) L
    rw [period_mobius _ _ τ (scalar_nonzero n hn τ hτ),smul_smul,
      mul_inv_cancel₀ (scalar_nonzero n hn τ hτ),one_smul]
  have hM : period τ (M*representation n)=periodScalar representation order n τ z := by
    rw [hperiod]
    exact congrArg (periodScalar representation order n τ)
      ((periodEquiv (translated n τ) (translated_positive n hn τ hτ)).apply_symm_apply z)
  have hN : period τ (N*representation n)=periodScalar representation order n τ w := by
    rw [hperiod]
    exact congrArg (periodScalar representation order n τ)
      ((periodEquiv (translated n τ) (translated_positive n hn τ hτ)).apply_symm_apply w)
  rw [←hM,←hN]
  change QuaternionicPeriodAlternating318.oriented
    ((periodEquiv τ hτ).symm (periodEquiv τ hτ (M*representation n)))
    ((periodEquiv τ hτ).symm (periodEquiv τ hτ (N*representation n)))=
      (reducedNorm (n:B):ℝ)*QuaternionicPeriodAlternating318.oriented M N
  rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply,oriented_right_det,representation_det]
end PELPositiveNormPeriodMap318
