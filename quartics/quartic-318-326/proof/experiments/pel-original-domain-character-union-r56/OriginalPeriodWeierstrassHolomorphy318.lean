module
public import OriginalPeriodWeierstrassCoordinates318
public section
noncomputable section
namespace OriginalPeriodWeierstrassHolomorphy318
open OriginalPeriodWeierstrassCoordinates318 OriginalComplexPeriodPair318
open ComplexLineLatticeAtlas318 ComplexLineLatticeMaps318 ComplexAffineFreeTranslation318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
local instance : ChartedSpace ℂ (Torus L) := chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := complex_manifold L

/-- Analyticity of the original periodic lift descends through the actual
quotient inverse charts on the unchanged complex atlas. -/
theorem descend_holomorphicAt (f : ℂ→ℂ) (hf : ∀ z (a : L),f (z+a.val)=f z)
    (z : ℂ) (hz : AnalyticAt ℂ f z) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (descend L f hf) (projection L z) := by
  have hlocal : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (descend L f hf ∘ (localChart L z).symm) z := by
    apply (contMDiffAt_iff_contDiffAt.mpr hz.contDiffAt).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun w => by
      change descend L f hf ((localChart L z).symm w)=f w
      rw [localChart_symm]
      rfl)
  have hp := localChart_center L z
  have hv : localChart L z (projection L z)=z :=
    (quotient_localHomeomorph L).localInverseAt_apply_self
  have hc := contMDiffAt_of_mem_maximalAtlas (chart_maximal L z) hp
  have hlocal' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (descend L f hf ∘ (localChart L z).symm) (localChart L z (projection L z)) := by
    rwa [hv]
  apply (hlocal'.comp _ hc).congr_of_eventuallyEq
  filter_upwards [(localChart L z).open_source.mem_nhds hp] with q hq
  simp only [Function.comp_apply,(localChart L z).left_inv hq]

lemma representative_not_lattice (z : ℂ) (hz : projection L z≠0) : z∉(pair L).lattice := by
  intro h
  exact hz ((QuotientAddGroup.eq_zero_iff).mpr ((pair_mem L z).mp h))

/-- Genuine coordinate holomorphy at every actual nonorigin torus point;
no values at the lattice pole are declared holomorphic. -/
theorem x_holomorphicAt (q : Torus L) (hq : q≠0) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (x L) q := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective L q
  exact descend_holomorphicAt L _ _ z
    ((pair L).analyticOnNhd_weierstrassP z (representative_not_lattice L z hq))

theorem y_holomorphicAt (q : Torus L) (hq : q≠0) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (y L) q := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective L q
  exact descend_holomorphicAt L _ _ z
    ((pair L).analyticOnNhd_derivWeierstrassP z (representative_not_lattice L z hq))
end OriginalPeriodWeierstrassHolomorphy318
