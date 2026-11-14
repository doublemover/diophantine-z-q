module
public import LegendreNativeGermHolomorphy318
public import LegendreInfinityBranchGerm318
public section
noncomputable section
namespace LegendreNativeInfinityGerm318
open Set Filter
open scoped Topology Manifold ContDiff
open LegendrePlaneOverlap318 LegendreIndependentGraphs318
variable (l:ℂ) [Fact (l≠0 ∧ l≠1)]
attribute [local instance] Classical.propDecidable

/-- The actual infinity-plane germ, totalized ONLY outside its equation
by the actual origin. Its near-center values never use this fallback. -/
@[expose] def point (U V:ℂ→ℂ) (w:ℂ) : InfinityPlane l :=
  if h:infinityEquation l (U w,V w)=0 then ⟨(U w,V w),h⟩ else origin l
lemma value (U V:ℂ→ℂ) (w:ℂ) (h:infinityEquation l (U w,V w)=0) :
    (point l U V w).val=(U w,V w) := by simp only [point,dif_pos h]
lemma center (U V:ℂ→ℂ) (hU:U 0=0) (hV:V 0=0) : point l U V 0=origin l := by
  apply Subtype.ext
  rw [value l U V 0 (by simp [hU,hV,infinityEquation]),hU,hV]
  rfl
lemma analytic (U V:ℂ→ℂ) (hU:AnalyticAt ℂ U 0) (hV:AnalyticAt ℂ V 0)
    (he:∀ᶠ w in 𝓝 (0:ℂ),LegendreInfinityBranchGerm318.equation l (U w) (V w)=0) :
    AnalyticAt ℂ (fun w=>(point l U V w).val) 0 := by
  apply (hU.prod hV).congr
  filter_upwards [he] with w hw
  exact (value l U V w hw).symm

/-- The native reciprocal formulas recover the ORIGINAL literal t,y,
not just their base projection, on the genuine overlap. -/
lemma literal_value (U V:ℂ→ℂ) (w t y:ℂ) (hy:y≠0)
    (he:infinityEquation l (U w,V w)=0)
    (hU:U w=(t-NormalizedLegendreProjectiveModel318.shift l)/y)
    (hV:V w=y⁻¹) :
    (LegendreLiteralCompletedAtlas318.literalFiniteEquiv l
      (toFinite l (point l U V w))).val=(t,y) := by
  have hv:(point l U V w).val.2≠0:=by
    rw [value l U V w he,hV]
    exact inv_ne_zero hy
  rw [LegendreNativeGermHolomorphy318.literal_infinity_coordinates l _ hv,
    value l U V w he,hU,hV]
  apply Prod.ext <;> dsimp <;> field_simp [hy] <;> ring
end LegendreNativeInfinityGerm318
