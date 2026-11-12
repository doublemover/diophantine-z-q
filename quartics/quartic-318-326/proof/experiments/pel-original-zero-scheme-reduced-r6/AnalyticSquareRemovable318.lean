module
public import BoundedVertexExtension318
public section
noncomputable section
namespace AnalyticSquareRemovable318
open Set Filter
open scoped Topology

/-- A punctured root of an analytic function has a constructed analytic
extension. Boundedness follows from its actual square equation; continuity
or a root choice at the missing point is NOT supplied. -/
theorem extend (f g:ℂ→ℂ) (hg:AnalyticAt ℂ g 0)
    (hd:∀ᶠw in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ f w)
    (he:∀ᶠw in 𝓝[≠] (0:ℂ),f w^2=g w) :
    ∃F:ℂ→ℂ,AnalyticAt ℂ F 0 ∧ F=ᶠ[𝓝[≠] (0:ℂ)] f ∧
      F 0^2=g 0 ∧ (∀ᶠw in 𝓝 (0:ℂ),F w^2=g w) := by
  have hb:∀ᶠw in 𝓝 (0:ℂ),‖g w‖<‖g 0‖+1:=
    hg.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  have hbound:∀ᶠw in 𝓝[≠] (0:ℂ),‖f w‖≤‖g 0‖+2:=by
    filter_upwards [he,hb.filter_mono nhdsWithin_le_nhds] with w hw hbw
    have hn:‖f w‖^2=‖g w‖:=by simpa only [norm_pow] using congrArg norm hw
    nlinarith [norm_nonneg (f w),norm_nonneg (g 0),sq_nonneg ‖g 0‖]
  obtain ⟨F,hF,hFf,hlim⟩:=BoundedVertexExtension318.analytic_extension hd (‖g 0‖+2) hbound
  have h0:F 0^2=g 0:=
    tendsto_nhds_unique (hlim.pow 2)
      ((hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  have hp:∀ᶠw in 𝓝[≠] (0:ℂ),F w^2=g w:=by
    filter_upwards [hFf,he] with w hf hs
    rw [hf,hs]
  have hall:∀ᶠw in 𝓝 (0:ℂ),F w^2=g w:=by
    filter_upwards [eventually_nhdsWithin_iff.mp hp] with w hw
    by_cases hz:w=0
    · simpa only [hz] using h0
    · exact hw hz
  exact ⟨F,hF,hFf,h0,hall⟩
end AnalyticSquareRemovable318
