module
public import ComplexSphereJoukowski318
public import PELActualConformalMirror318
public section
noncomputable section
namespace PELActualInteriorSphereMap318
open Set Metric Filter Topology
open scoped OnePoint Manifold ContDiff ComplexConjugate
open ComplexSphereCharts318 ComplexSphereJoukowski318 ReflectedDiskJoukowski318
open PELMaximalActualComplexDomain318 PELActualInteriorConformal318
set_option maxHeartbeats 2800000
local instance : ChartedSpace ℂ (OnePoint ℂ) := sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ) := sphere_manifold

@[expose] def sphereMap (e : OpenPartialHomeomorph ℂ ℂ) : ℂ → OnePoint ℂ :=
  fun z => joukowski (e z)

/-- The actual conformal replacement followed by z−1/z is holomorphic
into the STANDARD complex sphere at every interior point, including the
original center. It is not the earlier topological radial map. -/
theorem sphereMap_holomorphicAt (e : OpenPartialHomeomorph ℂ ℂ)
    (ha : ∀ z∈openDomain,AnalyticAt ℂ e z) {z : ℂ} (hz : z∈openDomain) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (sphereMap e) z :=
  (joukowski_holomorphic (e z)).comp z (contMDiffAt_iff_contDiffAt.mpr (ha z hz).contDiffAt)

/-- The disk interior has no second Joukowski preimage: the second algebraic
possibility forces product -1, impossible for two norms strictly below1. -/
theorem sphereMap_injective (e : OpenPartialHomeomorph ℂ ℂ)
    (hs : e.source=openDomain) (ht : e.target=ball 0 1) : InjOn (sphereMap e) openDomain := by
  intro z hz w hw heq
  have hz' : ‖e z‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using ht ▸ e.map_source (hs.symm ▸ hz)
  have hw' : ‖e w‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using ht ▸ e.map_source (hs.symm ▸ hw)
  rcases (sphere_fibers (e z) (e w)).mp heq with hsame | hprod
  · exact e.injOn (hs.symm ▸ hz) (hs.symm ▸ hw) hsame
  · have hn : ‖e z‖*‖e w‖=1 := by simpa only [norm_mul,norm_neg,norm_one] using congrArg norm hprod
    have hm := mul_le_mul_of_nonneg_left hw'.le (norm_nonneg (e z))
    nlinarith

/-- At the original reflection-fixed center, infinity is the actual target
point and the reciprocal coordinate has derivative -e′(center), nonzero
by positive normalization. This explicitly checks the pole's convention. -/
theorem center_pole (e : OpenPartialHomeomorph ℂ ℂ)
    (ha : ∀ z∈openDomain,AnalyticAt ℂ e z) (hzero : e center=0)
    (hre : 0<(deriv e center).re) :
    sphereMap e center=∞ ∧
      HasDerivAt (fun z => reciprocal (sphereMap e z)) (-deriv e center) center ∧
      -deriv e center≠0 := by
  have hr : HasDerivAt (fun z : ℂ => reciprocal (joukowski z)) (-1) (e center) := by
    rw [hzero]
    exact reciprocal_derivative
  have hc := hr.comp center (ha center center_mem).differentiableAt.hasDerivAt
  refine ⟨by simp only [sphereMap,hzero,joukowski,if_pos rfl],?_,?_⟩
  · simpa only [neg_one_mul] using hc
  · intro h
    have hd := neg_eq_zero.mp h
    rw [hd] at hre
    exact (lt_irrefl (0:ℝ)) hre

/-- A genuine standard-sphere holomorphic map is produced on the entire
original open halfcut. Boundary gluing and compact arithmetic descent
remain separate, so this does not declare MaximalBase biholomorphic to P1. -/
theorem actual_holomorphic_interior_sphere_map :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source=openDomain ∧ e.target=ball 0 1 ∧
      e center=0 ∧ (∀ z∈openDomain,e (-conj z)= -conj (e z)) ∧
      (∀ z∈openDomain,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (sphereMap e) z) ∧
      InjOn (sphereMap e) openDomain ∧ sphereMap e center=∞ ∧
      HasDerivAt (fun z => reciprocal (sphereMap e z)) (-deriv e center) center ∧
      -deriv e center≠0 := by
  obtain ⟨e,hs,ht,hzero,ha,hi,him,hre,hm⟩ := PELActualConformalMirror318.actual_symmetric_conformal_chart
  exact ⟨e,hs,ht,hzero,hm,fun z hz => sphereMap_holomorphicAt e ha hz,
    sphereMap_injective e hs ht,center_pole e ha hzero hre⟩
end PELActualInteriorSphereMap318
