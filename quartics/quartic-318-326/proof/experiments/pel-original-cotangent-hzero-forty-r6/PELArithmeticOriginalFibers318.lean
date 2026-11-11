module
public import PELArithmeticComplexFamily318
public section
noncomputable section
namespace PELArithmeticOriginalFibers318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELComplexPeriodSurface318 PELHolomorphicFamilyProjection318 PELOriginalHolomorphicFibers318
open PELPrincipalThreeFreeAction318 PELPrincipalProperAction318 PELPrincipalThreeCovering318
open PELArithmeticComplexFamily318
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000

/-- Literal fiber of the original arithmetic projection at the orbit of τ. -/
abbrev ArithmeticFiber (τ : HalfPlane) :=
  {p : ArithmeticTotal // arithmeticProjection p=baseQuotient τ}

theorem projection_smul (u : principalThree) (p : Total) : (u • p).1=u • p.1 := rfl

@[expose] def fiberMap (τ : HalfPlane) : Fiber τ → ArithmeticFiber τ :=
  fun p => ⟨totalQuotient p.val,congrArg baseQuotient p.property⟩

theorem fiberMap_continuous (τ : HalfPlane) : Continuous (fiberMap τ) :=
  (total_covering.continuous.comp continuous_subtype_val).subtype_mk _

/-- Exact base freeness rules out additional arithmetic identifications
inside ONE original surface fiber. -/
theorem fiberMap_injective (τ : HalfPlane) : Function.Injective (fiberMap τ) := by
  intro p q hpq
  have he : totalQuotient p.val=totalQuotient q.val := congrArg Subtype.val hpq
  obtain ⟨u,hu⟩ := total_covering.apply_eq_iff_mem_orbit.mp he
  have hbase : u • τ=τ := by
    have h := congrArg Prod.fst hu
    rw [projection_smul,q.property,p.property] at h
    exact h
  have hone : u=1 := no_base_stabilizer u τ hbase
  apply Subtype.ext
  simpa only [hone,one_smul] using hu.symm

/-- Every point of the arithmetic fiber has an original representative
above τ, obtained using the actual arithmetic group element in its base orbit. -/
theorem fiberMap_surjective (τ : HalfPlane) : Function.Surjective (fiberMap τ) := by
  intro p
  obtain ⟨x,hx⟩ := totalQuotient_surjective p.val
  have hb : baseQuotient x.1=baseQuotient τ := by
    have h := p.property
    rw [←hx,arithmetic_projection_square] at h
    exact h
  obtain ⟨u,hu⟩ := base_covering.apply_eq_iff_mem_orbit.mp hb
  have hy : (u⁻¹ • x).1=τ := by
    rw [projection_smul,←hu,inv_smul_smul]
  refine ⟨⟨u⁻¹ • x,hy⟩,?_⟩
  apply Subtype.ext
  change totalQuotient (u⁻¹ • x)=p.val
  rw [total_covering.map_smul,hx]

@[expose] def originalFiberEquiv (τ : HalfPlane) : Surface τ ≃ ArithmeticFiber τ :=
  (originalFiberHomeomorph τ).toEquiv.trans
    (Equiv.ofBijective (fiberMap τ) ⟨fiberMap_injective τ,fiberMap_surjective τ⟩)

theorem originalFiberEquiv_continuous (τ : HalfPlane) : Continuous (originalFiberEquiv τ) :=
  (fiberMap_continuous τ).comp (originalFiberHomeomorph τ).continuous

/-- Compactness is established on EVERY literal arithmetic fiber by the
actual surjective original-fiber map, with no properness/algebraization assumption. -/
theorem arithmeticFiber_compact (τ : HalfPlane) : CompactSpace (ArithmeticFiber τ) := by
  letI : CompactSpace (Fiber τ) := original_fiber_compact τ
  have h : IsCompact (Set.range (fiberMap τ)) := isCompact_range (fiberMap_continuous τ)
  rw [Set.range_eq_univ.mpr (fiberMap_surjective τ)] at h
  exact ⟨h⟩

local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold
local instance : ChartedSpace Ambient ArithmeticTotal := arithmeticTotalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω ArithmeticTotal := arithmeticTotal_manifold
variable (τ : HalfPlane)
local instance : DiscreteTopology (Periods τ) :=
  PELOriginalPeriodLattice318.original_discrete τ τ.property
local instance : ChartedSpace ComplexVectors (Surface τ) := surfaceCharts τ τ.property
local instance : IsManifold 𝓘(ℂ,ComplexVectors) ω (Surface τ) := surface_manifold τ τ.property

/-- The exact original surface maps holomorphically into the arithmetic
total space, using its ORIGINAL complex atlas and the actual quotient projection. -/
theorem originalFiberInclusion_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,Ambient) ω
      (fun p : Surface τ => (originalFiberEquiv τ p).val) :=
  totalQuotient_holomorphic.comp (PELOriginalHolomorphicFibers318.originalFiberInclusion_holomorphic τ)

/-- The entire original period projection is retained on the literal
arithmetic fiber, not merely an unnamed isomorphic compact surface. -/
theorem original_period_square (z : ComplexVectors) :
    (originalFiberEquiv τ (QuotientAddGroup.mk' (Periods τ) z)).val=
      totalQuotient (familyProjection (τ,z)) := by
  change totalQuotient (originalFiberInclusion τ (QuotientAddGroup.mk' (Periods τ) z))=_
  rw [originalFiberInclusion_mk]
end PELArithmeticOriginalFibers318
