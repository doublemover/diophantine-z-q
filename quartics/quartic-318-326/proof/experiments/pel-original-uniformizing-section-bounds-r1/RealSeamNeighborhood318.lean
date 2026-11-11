module
public import ModulusSchwarzExtension318
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public section
noncomputable section
namespace RealSeamNeighborhood318
open Set Filter Metric
open scoped Topology
open HolomorphicRectanglePrimitive318
set_option maxHeartbeats 2600000

/-- A genuine whole rectangle around a real seam point can be chosen
inside any prescribed neighborhood. Its upper and lower sides share the
same radius; no one-sided neighborhood is silently used as a full one. -/
theorem rectangle_in_neighborhood (x:ℝ) (S:Set ℂ) (hS:S∈𝓝 (x:ℂ)) :
    ∃r>0,openRectangle (x-r) (x+r) (-r) r⊆S := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨δ/4,by positivity,?_⟩
  intro z hz
  apply hsub
  rw [mem_ball,dist_eq_norm]
  have hre:|z.re-x|<δ/4 := abs_lt.mpr ⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩
  have him:|z.im|<δ/4 := abs_lt.mpr hz.2
  have hnorm:=Complex.norm_le_abs_re_add_abs_im (z-(x:ℂ))
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hnorm
  linarith

/-- Exact local upper-half-plane geometry gives an actual frontier point
of the original open domain. Closure is constructed by a path through
that original domain, not inferred from a picture. -/
theorem chart_seam_frontier (D:Set ℂ) (hD:IsOpen D)
    (e:OpenPartialHomeomorph ℂ ℂ) {w:ℂ} (hw:w∈e.target) (hwr:w.im=0)
    (hhalf:∀ᶠv in 𝓝 w,e.symm v∈D ↔ 0<v.im) : e.symm w∈frontier D := by
  let path:ℝ→ℂ := fun t=>w+Complex.I*t
  have hp:Tendsto path (𝓝[>] (0:ℝ)) (𝓝 w) := by
    have hc:Continuous path := by dsimp [path];fun_prop
    simpa only [path,Complex.ofReal_zero,mul_zero,add_zero] using
      (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hinside:∀ᶠt in 𝓝[>] (0:ℝ),e.symm (path t)∈D := by
    filter_upwards [hp.eventually hhalf,self_mem_nhdsWithin] with t ht htpos
    apply ht.mpr
    simpa [path,hwr] using htpos
  have hclosure:e.symm w∈closure D :=
    mem_closure_of_tendsto ((e.continuousAt_symm hw).tendsto.comp hp) hinside
  have hnot:e.symm w∉D := by
    intro hin
    have hh := hhalf.self_of_nhds
    have hpos := hh.mp hin
    simpa only [hwr,lt_self_iff_false] using hpos
  exact ⟨hclosure,by simpa only [hD.interior_eq] using hnot⟩
end RealSeamNeighborhood318
