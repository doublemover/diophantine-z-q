module
public import PELUnlevelledInertiaOrbits318
public import PELPositiveNormalizerEffective318
public section
noncomputable section
namespace PELUnlevelledNormalizerAction318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open QuaternionicUnitPeriodTransport318 QuaternionicPositiveDeterminant318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELNormalizerArithmeticBase318
open PELNormalizerPrincipalConjugation318 PELPositiveNormalizerNormOne318
open PELJointNormOneAction318 PELNormOneBaseAction318 PELEffectiveNormOneAction318
open PELPrincipalBaseHolomorphy318 PELPrincipalThreeCovering318 PELUnlevelledComplexBase318
open HolomorphicQuotientCoverMaps318
open scoped Manifold ContDiff
set_option maxHeartbeats 1700000

theorem original_norm_one_intertwining (g : positiveNormalizer) (u : normOneUnits) :
    (((globalConjugation g u).val:order):B)*(g.val:B)=(g.val:B)*((u.val:order):B) := by
  change ((g.val:B)*((u.val:order):B)*(↑g.val⁻¹:B))*(g.val:B)= _
  simp only [mul_assoc,Units.inv_val,mul_one]

theorem matrix_intertwining (g : positiveNormalizer) (u : normOneUnits) :
    unitMatrix representation order (globalConjugation g u).val*PELPositiveNormalizerMobius318.matrix g=
      PELPositiveNormalizerMobius318.matrix g*unitMatrix representation order u.val := by
  change representation (((globalConjugation g u).val:order):B)*representation (g.val:B)=
    representation (g.val:B)*representation ((u.val:order):B)
  rw [←map_mul,←map_mul,original_norm_one_intertwining]

theorem base_equivariant (g : positiveNormalizer) (u : normOneUnits) (τ : HalfPlane) :
    baseAction g (u • τ)=globalConjugation g u • baseAction g τ := by
  apply Subtype.ext
  change mobius (PELPositiveNormalizerMobius318.matrix g) (mobius (unitMatrix representation order u.val) τ)=
    mobius (unitMatrix representation order (globalConjugation g u).val)
      (mobius (PELPositiveNormalizerMobius318.matrix g) τ)
  have hu : 0<(unitMatrix representation order u.val).det := by rw [u.property] <;> norm_num
  have hv : 0<(unitMatrix representation order (globalConjugation g u).val).det := by
    rw [(globalConjugation g u).property] <;> norm_num
  rw [mobius_comp_positive _ _ (matrix_positive g) hu τ τ.property,
    mobius_comp_positive _ _ hv (matrix_positive g) τ τ.property,matrix_intertwining]

/-- Full positive-normalizer descent on the actual unlevelled complex
base, using ORIGINAL norm-one conjugation rather than an assumed deck action. -/
@[expose] def coarseAction (g : positiveNormalizer) : UnlevelledBase → UnlevelledBase :=
  Quotient.map' (baseAction g) (by
    rintro τ σ ⟨v,hv⟩
    obtain ⟨u,hu⟩ := effectiveMap_surjective v
    rw [←hu] at hv
    refine ⟨effectiveMap (globalConjugation g u),?_⟩
    change globalConjugation g u • baseAction g σ=baseAction g τ
    rw [←base_equivariant,hv])

theorem coarseAction_square (g : positiveNormalizer) (τ : HalfPlane) :
    coarseAction g (projection τ)=projection (baseAction g τ) := rfl

theorem coarseAction_one (x : UnlevelledBase) : coarseAction 1 x=x := by
  obtain ⟨τ,rfl⟩ := projection_surjective x
  rw [coarseAction_square,baseAction_one]

theorem coarseAction_mul (g h : positiveNormalizer) (x : UnlevelledBase) :
    coarseAction (g*h) x=coarseAction g (coarseAction h x) := by
  obtain ⟨τ,rfl⟩ := projection_surjective x
  rw [coarseAction_square,baseAction_mul,coarseAction_square,coarseAction_square]

@[expose] def coarseEquiv (g : positiveNormalizer) : UnlevelledBase ≃ UnlevelledBase where
  toFun := coarseAction g
  invFun := coarseAction g⁻¹
  left_inv x := by rw [←coarseAction_mul,inv_mul_cancel,coarseAction_one]
  right_inv x := by rw [←coarseAction_mul,mul_inv_cancel,coarseAction_one]

local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

theorem coarseAction_holomorphic (g : positiveNormalizer) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (coarseAction g) :=
  descended_holomorphic projection covering effective_holomorphic
    (coarseAction g) (fun τ => projection (baseAction g τ))
    (PELUnlevelledComplexBase318.projection_holomorphic.comp (baseAction_holomorphic g))
    (coarseAction_square g)

theorem coarseEquiv_holomorphic (g : positiveNormalizer) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (coarseEquiv g) := coarseAction_holomorphic g

theorem coarseEquiv_symm_holomorphic (g : positiveNormalizer) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (coarseEquiv g).symm := coarseAction_holomorphic g⁻¹

theorem forgetLevel_equivariant (g : positiveNormalizer) (x : ArithmeticBase) :
    forgetLevel (arithmeticAction g x)=coarseAction g (forgetLevel x) := by
  obtain ⟨τ,rfl⟩ := baseQuotient_surjective x
  rw [arithmeticAction_square,forgetLevel_square,forgetLevel_square,coarseAction_square]
end PELUnlevelledNormalizerAction318
