module
public import ComplexSphereCharts318
public import ReflectedDiskJoukowskiTopology318
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public section
noncomputable section
namespace ComplexSphereJoukowski318
open Set Metric Filter Topology
open scoped OnePoint Manifold ContDiff
open ComplexSphereCharts318 ReflectedDiskJoukowski318 ReflectedDiskJoukowskiTopology318
open SphereInversion318
set_option maxHeartbeats 2400000
local instance : ChartedSpace ℂ (OnePoint ℂ) := sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ) := sphere_manifold

/-- Test holomorphy in either of the actual standard sphere charts,
retaining the given map and existing sphere topology. -/
theorem holomorphic_of_coordinate (F : ℂ → OnePoint ℂ) {z : ℂ}
    (hF : ContinuousAt F z) (b : Bool) (hz : F z∈(chart b).source)
    (ha : AnalyticAt ℂ (fun w => chart b (F w)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F z := by
  have hm : chart b∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ) :=
    IsManifold.subset_maximalAtlas ⟨b,rfl⟩
  have hi := contMDiffAt_symm_of_mem_maximalAtlas hm ((chart b).map_source hz)
  have hc : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w => chart b (F w)) z :=
    contMDiffAt_iff_contDiffAt.mpr ha.contDiffAt
  apply (hi.comp z hc).congr_of_eventuallyEq
  filter_upwards [hF.eventually ((chart b).open_source.mem_nhds hz)] with w hw
  exact ((chart b).left_inv hw).symm

/-- The finite-coordinate expression agrees with the already constructed
sphere map away from its genuine pole. -/
theorem affine_formula {z : ℂ} (hz : z≠0) : affine (joukowski z)=z-z⁻¹ := by
  rw [joukowski,if_neg hz,affine_coe]

/-- The reciprocal coordinate extends THROUGH the pole as z/(z²−1).
This identity includes z=0 and has not discarded the center. -/
theorem reciprocal_coordinate (z : ℂ) (hz : z^2-1≠0) :
    reciprocal (joukowski z)=z/(z^2-1) := by
  rw [←reciprocal_formula z hz,reciprocal_value,inversion_involutive,affine_coe]

/-- The independent standard-sphere map z−1/z is genuinely holomorphic,
including its pole at0 in the reciprocal target chart. -/
theorem joukowski_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω joukowski := by
  intro z
  by_cases hz : z=0
  · subst z
    have hp : joukowski 0∈(chart true).source := by
      simpa only [joukowski,if_pos rfl,chart,if_true] using reciprocal_mem_infty
    apply holomorphic_of_coordinate joukowski joukowski_continuous.continuousAt true hp
    have ha : AnalyticAt ℂ (fun w : ℂ => w/(w^2-1)) 0 :=
      analyticAt_id.div ((analyticAt_id.pow 2).sub analyticAt_const) (by norm_num)
    apply ha.congr
    have hn : ∀ᶠ w : ℂ in 𝓝 0,w^2-1≠0 :=
      ((continuousAt_id.pow 2).sub continuousAt_const).eventually
        (eventually_ne_nhds (by norm_num : (0:ℂ)^2-1≠0))
    filter_upwards [hn] with w hw
    exact (reciprocal_coordinate w hw).symm
  · have hp : joukowski z∈(chart false).source := by
      change joukowski z∈affine.source
      rw [joukowski,if_neg hz]
      exact affine_mem _
    apply holomorphic_of_coordinate joukowski joukowski_continuous.continuousAt false hp
    apply (analyticAt_id.sub (analyticAt_id.inv hz)).congr
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact (affine_formula hw).symm

/-- The pole is simple: the actual reciprocal chart derivative is -1. -/
theorem reciprocal_derivative :
    HasDerivAt (fun z : ℂ => reciprocal (joukowski z)) (-1) 0 := by
  have hh : HasDerivAt (fun z : ℂ => z/(z^2-1)) (-1) 0 := by
    convert (hasDerivAt_id (0:ℂ)).div
      (((hasDerivAt_id (0:ℂ)).pow 2).sub_const 1) (by norm_num) using 1 <;> norm_num <;> rfl
  apply hh.congr_of_eventuallyEq
  have hn : ∀ᶠ w : ℂ in 𝓝 0,w^2-1≠0 :=
    ((continuousAt_id.pow 2).sub continuousAt_const).eventually
      (eventually_ne_nhds (by norm_num : (0:ℂ)^2-1≠0))
  filter_upwards [hn] with w hw
  exact reciprocal_coordinate w hw
end ComplexSphereJoukowski318
