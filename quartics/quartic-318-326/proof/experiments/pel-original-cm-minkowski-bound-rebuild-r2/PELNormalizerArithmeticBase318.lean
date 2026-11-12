module
public import PELPositiveNormalizerMobius318
public section
noncomputable section
namespace PELNormalizerArithmeticBase318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open QuaternionicPositiveDeterminant318 PELPositiveOrderNormalizer318
open PELNormalizerPrincipalConjugation318 PELPositiveNormalizerMobius318
open PELPrincipalThreeFreeAction318 PELPrincipalThreeCovering318
open PELPrincipalBaseHolomorphy318 PELArithmeticComplexFamily318 HolomorphicQuotientCoverMaps318
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold
local instance : ChartedSpace ℂ ArithmeticBase := arithmeticBaseCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω ArithmeticBase := arithmeticBase_manifold

theorem baseAction_holomorphic (g : positiveNormalizer) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (baseAction g) := by
  apply lift_holomorphic
  intro τ
  have hn : AnalyticAt ℂ (fun z : ℂ => (matrix g 0 0:ℂ)*z+(matrix g 0 1:ℂ)) τ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hd : AnalyticAt ℂ (denominator (matrix g)) τ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hm : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (mobius (matrix g)) (τ:ℂ) :=
    contMDiffAt_iff_contDiffAt.mpr
      (hn.div hd (QuaternionicPositiveDeterminant318.denominator_nonzero
        _ (matrix_positive g) τ τ.property)).contDiffAt
  exact hm.comp τ (inclusion_holomorphic τ)

/-- The original positive normalizer acts on the LITERAL fine arithmetic
base because it normalizes the SAME principal-three subgroup. -/
@[expose] def arithmeticAction (g : positiveNormalizer) : ArithmeticBase → ArithmeticBase :=
  Quotient.map' (baseAction g) (by
    rintro τ σ ⟨u,hu⟩
    refine ⟨principalConjugation g u,?_⟩
    rw [←baseAction_equivariant,hu])

theorem arithmeticAction_square (g : positiveNormalizer) (τ : HalfPlane) :
    arithmeticAction g (baseQuotient τ)=baseQuotient (baseAction g τ) := rfl

theorem arithmeticAction_one (x : ArithmeticBase) : arithmeticAction 1 x=x := by
  obtain ⟨τ,rfl⟩ := baseQuotient_surjective x
  rw [arithmeticAction_square,baseAction_one]

theorem arithmeticAction_mul (g h : positiveNormalizer) (x : ArithmeticBase) :
    arithmeticAction (g*h) x=arithmeticAction g (arithmeticAction h x) := by
  obtain ⟨τ,rfl⟩ := baseQuotient_surjective x
  rw [arithmeticAction_square,baseAction_mul,arithmeticAction_square,arithmeticAction_square]

@[expose] def arithmeticEquiv (g : positiveNormalizer) : ArithmeticBase ≃ ArithmeticBase where
  toFun := arithmeticAction g
  invFun := arithmeticAction g⁻¹
  left_inv x := by rw [←arithmeticAction_mul,inv_mul_cancel,arithmeticAction_one]
  right_inv x := by rw [←arithmeticAction_mul,mul_inv_cancel,arithmeticAction_one]

/-- Holomorphy uses the existing quotient atlas and its genuine covering,
not a newly imposed complex structure on the underlying quotient set. -/
theorem arithmeticAction_holomorphic (g : positiveNormalizer) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (arithmeticAction g) :=
  descended_holomorphic baseQuotient base_covering principal_base_holomorphic
    (arithmeticAction g) (fun τ => baseQuotient (baseAction g τ))
    (baseQuotient_holomorphic.comp (baseAction_holomorphic g)) (arithmeticAction_square g)

theorem arithmeticEquiv_holomorphic (g : positiveNormalizer) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (arithmeticEquiv g) := arithmeticAction_holomorphic g

theorem arithmeticEquiv_symm_holomorphic (g : positiveNormalizer) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (arithmeticEquiv g).symm := arithmeticAction_holomorphic g⁻¹
end PELNormalizerArithmeticBase318
