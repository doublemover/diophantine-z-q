module
public import WeierstrassInfinityChart318
public section
noncomputable section
namespace OriginalPeriodInfinityExtension318
open OriginalComplexPeriodPair318 OriginalPeriodWeierstrassCoordinates318
open ComplexLineLatticeAtlas318 ComplexLineLatticeMaps318 ComplexAffineFreeTranslation318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 3000000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
local instance : ChartedSpace ℂ (Torus L) := chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := complex_manifold L

@[expose] def poleChart := localChart L (0:ℂ)
lemma pole_source : (0 : Torus L)∈(poleChart L).source := by
  simpa only [map_zero] using localChart_center L (0:ℂ)
lemma pole_value : poleChart L (0:Torus L)=0 := by
  simpa only [map_zero] using (quotient_localHomeomorph L).localInverseAt_apply_self (x := (0:ℂ))
lemma pole_holomorphic : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (poleChart L) (0:Torus L) :=
  contMDiffAt_of_mem_maximalAtlas (chart_maximal L 0) (pole_source L)

/-- The genuine Y-nonzero projective coordinates at the original quotient
origin. Their values are constructed from regularized Weierstrass germs. -/
@[expose] def u (q : Torus L) : ℂ := WeierstrassInfinityChart318.u (pair L) (poleChart L q)
@[expose] def v (q : Torus L) : ℂ := WeierstrassInfinityChart318.v (pair L) (poleChart L q)
lemma u_zero : u L 0=0 := by rw [u,pole_value,WeierstrassInfinityChart318.u_zero]
lemma v_zero : v L 0=0 := by rw [v,pole_value,WeierstrassInfinityChart318.v_zero]

theorem infinity_holomorphic :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (u L) (0:Torus L) ∧
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (v L) (0:Torus L) := by
  have hu : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (WeierstrassInfinityChart318.u (pair L)) (poleChart L (0:Torus L)) := by
    rw [pole_value]
    exact contMDiffAt_iff_contDiffAt.mpr (WeierstrassInfinityChart318.u_analytic (pair L)).contDiffAt
  have hv : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (WeierstrassInfinityChart318.v (pair L)) (poleChart L (0:Torus L)) := by
    rw [pole_value]
    exact contMDiffAt_iff_contDiffAt.mpr (WeierstrassInfinityChart318.v_analytic (pair L)).contDiffAt
  exact ⟨hu.comp _ (pole_holomorphic L),hv.comp _ (pole_holomorphic L)⟩

lemma chart_tendsto : Tendsto (poleChart L) (𝓝 (0:Torus L)) (𝓝 (0:ℂ)) := by
  simpa only [pole_value] using (pole_holomorphic L).continuousAt

/-- The projective cubic holds through the original quotient pole on an
actual neighborhood, with infinity represented by u=v=0. -/
theorem infinity_cubic : ∀ᶠ q in 𝓝 (0:Torus L),
    v L q=4*u L q^3-(pair L).g₂*u L q*v L q^2-(pair L).g₃*v L q^3 :=
  (chart_tendsto L).eventually (WeierstrassInfinityChart318.cubic_eventually (pair L))

/-- On the genuine punctured overlap these constructed pole coordinates
are EXACTLY x/y and 1/y for the earlier original affine coordinates. -/
theorem affine_overlap : ∀ᶠ q in 𝓝 (0:Torus L), q≠0 →
    y L q≠0 ∧ u L q=x L q/y L q ∧ v L q=1/y L q := by
  have hy : ∀ᶠ z in 𝓝 (0:ℂ),WeierstrassInfinityChart318.denominatorY (pair L) z≠0 :=
    (WeierstrassInfinityChart318.denominator_analytic (pair L)).continuousAt.eventually
      (eventually_ne_nhds (WeierstrassInfinityChart318.denominator_ne (pair L)))
  filter_upwards [(poleChart L).open_source.mem_nhds (pole_source L),
    (chart_tendsto L).eventually hy] with q hq hden
  intro hne
  have hpc : projection L (poleChart L q)=q := by
    simpa only [poleChart,localChart_symm] using (poleChart L).left_inv hq
  have hz : poleChart L q≠0 := by
    intro h
    rw [h,map_zero] at hpc
    exact hne hpc.symm
  have hh := WeierstrassInfinityChart318.affine_overlap (pair L) (poleChart L q) hz hden
  have hx := x_projection L (poleChart L q)
  have hyy := y_projection L (poleChart L q)
  rw [hpc] at hx hyy
  have hnon : y L q≠0 := by
    rw [hyy]
    intro h
    rw [WeierstrassInfinityChart318.denominator_scaled (pair L) (poleChart L q) hz,
      h,mul_zero] at hden
    exact hden rfl
  exact ⟨hnon,by simpa only [u,v,←hx,←hyy] using hh⟩
end OriginalPeriodInfinityExtension318
