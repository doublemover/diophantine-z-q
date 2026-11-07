module
public import ChordFlow318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace MeromorphicContinuation318
set_option maxHeartbeats 0

/-- A genuine meromorphic germ equality propagates to punctured neighborhoods everywhere. -/
theorem punctured_eq {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g)
    {x : ℂ} (he : f =ᶠ[𝓝 x] g) (y : ℂ) : f =ᶠ[𝓝[≠] y] g := by
  have hd : MeromorphicOn (fun z => f z-g z) Set.univ := fun z _ => (hf z).sub (hg z)
  have hx : meromorphicOrderAt (fun z => f z-g z) x = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
    simp [hz]
  have hy := hd.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ x) (Set.mem_univ y) hx
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hy] with z hz
  exact sub_eq_zero.mp hz

lemma value_eq {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g)
    {x : ℂ} (he : f =ᶠ[𝓝 x] g) (y : ℂ)
    (hfy : ContinuousAt f y) (hgy : ContinuousAt g y) : f y=g y := by
  have he' := punctured_eq hf hg he y
  have ht := (hfy.tendsto.mono_left nhdsWithin_le_nhds).congr' he'
  exact tendsto_nhds_unique ht (hgy.tendsto.mono_left nhdsWithin_le_nhds)
end MeromorphicContinuation318
