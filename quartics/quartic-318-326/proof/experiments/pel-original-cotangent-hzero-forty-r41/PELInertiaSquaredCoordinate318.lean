module
public import PELCoarseInertiaCoordinate318
public section
noncomputable section
namespace PELInertiaSquaredCoordinate318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318 PELJointComplexAtlas318
open PELPrincipalBaseHolomorphy318 PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELUnlevelledNormalizerAction318 PELCoarseInertiaCoordinate318 ComplexTwoPointCoordinate318
open PELQuaternionAlgebra318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1800000
local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- The constructed local coordinate is holomorphic for the ORIGINAL
coarse atlas, not a replacement complex structure chosen to fit the action. -/
theorem chart_holomorphic (τ : HalfPlane) (x : UnlevelledBase)
    (hx : x∈(inertiaChart τ).source) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (inertiaChart τ) x := by
  let A := HolomorphicQuotientCoverCharts318.quotientChart projection covering τ
  have hA : A∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase :=
    HolomorphicQuotientCoverMaps318.quotientChart_maximal projection covering
      PELEffectiveNormOneAction318.effective_holomorphic τ
  have hxA : x∈A.source := hx.1
  have hne : A x≠star (τ:ℂ) := hx.2
  have hC : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (coordinate (τ:ℂ) (star (τ:ℂ))) (A x) :=
    contMDiffAt_iff_contDiffAt.mpr (coordinate_analytic _ _ _ hne).contDiffAt
  exact hC.comp x (contMDiffAt_of_mem_maximalAtlas hA hxA)

theorem chart_inverse_holomorphic (τ : HalfPlane) (z : ℂ)
    (hz : z∈(inertiaChart τ).target) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (inertiaChart τ).symm z := by
  let A := HolomorphicQuotientCoverCharts318.quotientChart projection covering τ
  have hA : A∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase :=
    HolomorphicQuotientCoverMaps318.quotientChart_maximal projection covering
      PELEffectiveNormOneAction318.effective_holomorphic τ
  have hne : z≠1 := hz.1
  have hzA : inverse (τ:ℂ) (star (τ:ℂ)) z∈A.target := hz.2
  have hC : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (inverse (τ:ℂ) (star (τ:ℂ))) z :=
    contMDiffAt_iff_contDiffAt.mpr (inverse_analytic _ _ _ hne).contDiffAt
  exact (contMDiffAt_symm_of_mem_maximalAtlas hA hzA).comp z hC

@[expose] def squaredCoordinate (τ : HalfPlane) (x : UnlevelledBase) : ℂ := inertiaChart τ x^2

theorem actual_square_model (τ : HalfPlane) (z : ℂ) (hz : z∈(inertiaChart τ).target) :
    squaredCoordinate τ ((inertiaChart τ).symm z)=z^2 := by
  unfold squaredCoordinate
  rw [(inertiaChart τ).right_inv hz]

theorem squared_local_invariant (g : positiveNormalizer) (τ : HalfPlane)
    (hfix : baseAction g τ=τ) (htrace : reducedTrace (g.val:B)=0) :
    (fun x => squaredCoordinate τ (coarseAction g x)) =ᶠ[𝓝 (projection τ)]
      squaredCoordinate τ := by
  filter_upwards [local_negation g τ hfix htrace] with x hx
  simp only [squaredCoordinate,hx,neg_sq]

theorem complex_square_fiber (z w : ℂ) : z^2=w^2 ↔ z=w ∨ z= -w := by
  constructor
  · intro h
    have hm : (z-w)*(z+w)=0 := by linear_combination h
    rcases mul_eq_zero.mp hm with he | he
    · exact Or.inl (sub_eq_zero.mp he)
    · exact Or.inr (by linear_combination he)
  · rintro (rfl | rfl) <;> simp

/-- On the actual chart, equality of the proposed quotient coordinate is
EXACTLY the original two-point stabilizer orbit wherever its local sign law
holds. This is not merely a derivative or set-theoretic multiplicity count. -/
theorem squared_fiber_iff (g : positiveNormalizer) (τ : HalfPlane) (x y : UnlevelledBase)
    (hx : x∈(inertiaChart τ).source) (hy : y∈(inertiaChart τ).source)
    (hgy : coarseAction g y∈(inertiaChart τ).source)
    (he : inertiaChart τ (coarseAction g y)= -inertiaChart τ y) :
    squaredCoordinate τ x=squaredCoordinate τ y ↔ x=y ∨ x=coarseAction g y := by
  rw [squaredCoordinate,squaredCoordinate,complex_square_fiber]
  constructor
  · rintro (h | h)
    · exact Or.inl ((inertiaChart τ).injOn hx hy h)
    · exact Or.inr ((inertiaChart τ).injOn hx hgy (h.trans he.symm))
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr he
end PELInertiaSquaredCoordinate318
