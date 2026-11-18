module
public import OriginalArchimedeanSectionCoefficient318
public section
noncomputable section
namespace OriginalArchimedeanBranchDerivative318
open NumberField OriginalPointFinitePlaceRoots318 OriginalArchimedeanMarkedPoint318
open OriginalArchimedeanSectionCoefficient318 FourRootNormalizedPointCharts318
open LiteralMetricExtension318 Filter
open scoped Topology
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t))

include hn in
/-- Genuine local original signed coordinate functions on an actual
literal t chart. The differential multiplier used by the arithmetic
frame norm is THEIR derivative, not a scalar inferred from a norm bound. -/
theorem exists_chart : ∃ e : OpenPartialHomeomorph (FinitePoints contacts) ℂ,
    point c t w∈e.source ∧ (∀ q,e q=q.val.1) ∧
    ∀ i : Fin 4,
      let Y : ℂ → ℂ := fun z => twistRoot c i*(e.symm z).val.2 i
      AnalyticAt ℂ Y (t:ℂ) ∧ Y (t:ℂ)=markedRoot c t w i ∧
      (∀ᶠ z in 𝓝 (t:ℂ),Y z^2=((c i:ℚ):ℂ)*(z-contacts i)) ∧
      deriv Y (t:ℂ)=branchDerivative c t w i := by
  obtain ⟨e,he,ha,hA⟩ := FourRootSpecifiedFiniteCharts318.exists_regular contacts
    (point c t w) (fun i => div_ne_zero (markedRoot_ne c t hn w i) (twistRoot_ne c i))
  have het : (t:ℂ)∈e.target := by simpa only [ha] using e.map_source he
  have hinv : e.symm (t:ℂ)=point c t w := by
    simpa only [ha] using e.left_inv he
  refine ⟨e,he,ha,?_⟩
  intro i
  dsimp only
  let Y : ℂ → ℂ := fun z => twistRoot c i*(e.symm z).val.2 i
  have hY : AnalyticAt ℂ Y (t:ℂ) := analyticAt_const.mul
    (((ContinuousLinearMap.proj (R:=ℂ) i).analyticAt _).comp
      (analyticAt_snd.comp (hA _ het)))
  have hYt : Y (t:ℂ)=markedRoot c t w i := by
    dsimp only [Y]
    rw [hinv,mul_comm]
    exact point_root c t w i
  have hsq : ∀ᶠ z in 𝓝 (t:ℂ),Y z^2=((c i:ℚ):ℂ)*(z-contacts i) := by
    filter_upwards [e.open_target.mem_nhds het] with z hz
    have hb : (e.symm z).val.1=z := by rw [←ha,e.right_inv hz]
    dsimp only [Y]
    rw [mul_pow,twistRoot_square,(e.symm z).property i,hb]
  have hleft := hY.differentiableAt.hasDerivAt.pow 2
  have hright : HasDerivAt (fun z : ℂ => ((c i:ℚ):ℂ)*(z-contacts i))
      ((c i:ℚ):ℂ) (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).sub_const (contacts i)).const_mul ((c i:ℚ):ℂ)
  have heq := hleft.unique (hright.congr_of_eventuallyEq hsq)
  have hd : deriv Y (t:ℂ)=branchDerivative c t w i := by
    rw [branchDerivative]
    apply (eq_div_iff (mul_ne_zero (by norm_num) (markedRoot_ne c t hn w i))).mpr
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,hYt] at heq
    linear_combination heq
  exact ⟨hY,hYt,hsq,hd⟩
end OriginalArchimedeanBranchDerivative318
