module
public import OriginalPeriodProjectiveModel318
public section
noncomputable section
namespace OriginalPeriodNativeChartGerms318
open OriginalComplexPeriodPair318 OriginalPeriodWeierstrassCoordinates318
open OriginalPeriodProjectiveModel318 ComplexAffineFreeTranslation318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 2000000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
local instance : ChartedSpace ℂ (Torus L) := ComplexLineLatticeAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := ComplexLineLatticeAtlas318.complex_manifold L

/-- Genuine native Y=1 coordinates for [P:Pprime/2:1]. The factor TWO
is necessary: the earlier raw cubic used y=Pprime, not native y=Pprime/2. -/
@[expose] def nativeU (q : Torus L) : ℂ := 2*OriginalPeriodInfinityExtension318.u L q
@[expose] def nativeV (q : Torus L) : ℂ := 2*OriginalPeriodInfinityExtension318.v L q
lemma nativeU_zero : nativeU L 0=0 := by simp [nativeU,OriginalPeriodInfinityExtension318.u_zero]
lemma nativeV_zero : nativeV L 0=0 := by simp [nativeV,OriginalPeriodInfinityExtension318.v_zero]

theorem holomorphic :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (nativeU L) (0:Torus L) ∧
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (nativeV L) (0:Torus L) := by
  have hh := OriginalPeriodInfinityExtension318.infinity_holomorphic L
  exact ⟨contMDiffAt_const.mul hh.1,contMDiffAt_const.mul hh.2⟩

/-- The literal Y=1 equation of the independent projective scheme holds
on an actual original neighborhood, including its actual infinity. -/
theorem infinity_equation : ∀ᶠ q in 𝓝 (0:Torus L),
    nativeV L q-nativeU L q^3-A L*nativeU L q*nativeV L q^2-B L*nativeV L q^3=0 := by
  filter_upwards [OriginalPeriodInfinityExtension318.infinity_cubic L] with q hq
  dsimp [nativeU,nativeV,A,B]
  linear_combination 2*hq

/-- Exact homogeneous projective overlap with the original finite native
coordinates. A division by a zero affine coordinate is never admitted. -/
theorem overlap : ∀ᶠ q in 𝓝 (0:Torus L),q≠0 →
    y L q/2≠0 ∧ nativeU L q=x L q/(y L q/2) ∧ nativeV L q=1/(y L q/2) := by
  filter_upwards [OriginalPeriodInfinityExtension318.affine_overlap L] with q hq
  intro hn
  obtain ⟨hy,hu,hv⟩ := hq hn
  refine ⟨div_ne_zero hy (by norm_num),?_,?_⟩
  · rw [nativeU,hu]
    field_simp [hy] <;> ring
  · rw [nativeV,hv]
    field_simp [hy] <;> ring

/-- In the ORIGINAL lattice local parameter the native infinity
coordinate has derivative -1. Thus the scaling matches the actual
projective algebraic convention rather than only the cubic equation. -/
theorem native_infinity_derivative :
    HasDerivAt (fun z : ℂ => 2*WeierstrassInfinityChart318.u (pair L) z) (-1) 0 := by
  convert (WeierstrassInfinityChart318.u_hasDerivAt (pair L)).const_mul 2 using 1 <;> norm_num
end OriginalPeriodNativeChartGerms318
