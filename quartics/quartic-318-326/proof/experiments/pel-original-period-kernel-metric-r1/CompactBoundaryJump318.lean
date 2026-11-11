module
public import ConformalBoundaryModulus318
public import Mathlib.Topology.MetricSpace.Thickening
public section
noncomputable section
namespace CompactBoundaryJump318
open Set Metric Filter
open scoped Topology ComplexConjugate
set_option maxHeartbeats 2400000

/-- Relative limits on a compact boundary set give ONE uniform collar.
No boundary value, or continuity outside the original approach set, is
assumed. The collar comes from compactness, not an exchange of limits. -/
theorem uniform_zero_near_compact (U K : Set ℂ) (hK : IsCompact K)
    (f : ℂ → ℂ) (hf : ∀x∈K,Tendsto f (𝓝[U] x) (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    ∃δ>0,∀z∈thickening δ K,z∈U → ‖f z‖<ε := by
  let S : Set ℂ := {z | z∈U → ‖f z‖<ε}
  have hKS : K⊆interior S := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    have hh : ∀ᶠz in 𝓝[U] x,‖f z‖<ε := by
      simpa only [mem_ball,dist_zero_right] using
        (hf x hx).eventually (ball_mem_nhds (0:ℂ) hε)
    exact eventually_nhdsWithin_iff.mp hh
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_thickening_subset_open isOpen_interior hKS
  exact ⟨δ,hδ,fun z hz => interior_subset (hsub hz)⟩

/-- The same compact collar applies to the genuine reciprocal-conjugate
jump using only boundary MODULUS limits. -/
theorem uniform_reflected_jump (U K : Set ℂ) (hK : IsCompact K)
    (f : ℂ → ℂ)
    (hf : ∀x∈K,Tendsto (fun z=>‖f z‖) (𝓝[U] x) (𝓝 1))
    {ε : ℝ} (hε : 0<ε) :
    ∃δ>0,∀z∈thickening δ K,z∈U → ‖f z-(conj (f z))⁻¹‖<ε :=
  uniform_zero_near_compact U K hK _
    (fun x hx=>ConformalBoundaryModulus318.reflected_jump_tendsto_zero _ f (hf x hx)) hε

/-- A compact horizontal edge segment has uniform jump control on all
parallel sufficiently close upper segments, including both endpoints. -/
theorem uniform_horizontal_jump (f : ℂ → ℂ) (a b : ℝ)
    (hf : ∀x∈Icc a b,Tendsto f (𝓝[{z:ℂ | 0<z.im}] (x:ℂ)) (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    ∃δ>0,∀t:ℝ,0<t → t<δ → ∀x∈Icc a b,‖f ((x:ℂ)+Complex.I*t)‖<ε := by
  let K : Set ℂ := Complex.ofReal '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  obtain ⟨δ,hδ,hbound⟩ := uniform_zero_near_compact {z:ℂ | 0<z.im} K hK f
    (by rintro z ⟨x,hx,rfl⟩; exact hf x hx) hε
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ x hx
  apply hbound
  · apply mem_thickening_iff.mpr
    refine ⟨(x:ℂ),⟨x,hx,rfl⟩,?_⟩
    simpa [dist_eq_norm,norm_mul,Complex.norm_real,abs_of_pos ht] using htδ
  · simpa using ht
end CompactBoundaryJump318
