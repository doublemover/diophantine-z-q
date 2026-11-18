module
public import ContactMetricSections318
public import InducedLattice318
public section
noncomputable section
namespace DirectHodgeSectionHeight318
open NumberField SectionHeight318
variable {K : Type*} [Field K] [NumberField K]

/-- Auxiliary comparison norm only. The given Hodge frame H is never chosen
or modified to fit the sections; no claim is made that this auxiliary frame
is the geometric cotangent metric of any model. -/
@[expose] def comparisonFrame (H : FrameNorms K) : FrameNorms K :=
  InducedLattice318.induced (InducedLattice318.square H) (210:K)⁻¹ (inv_ne_zero (by norm_num))

theorem comparison_arch (H : FrameNorms K) (w : InfinitePlace K) :
    (comparisonFrame H).arch w=(H.arch w)^2 := rfl

theorem comparison_finite (H : FrameNorms K) (w : FinitePlace K) :
    (comparisonFrame H).finiteNorm w=(H.finiteNorm w)^2*w (210:K) := by
  change (H.finiteNorm w)^2 / w.val ((210:K)⁻¹) = _
  rw [map_inv₀,div_inv_eq_mul]

private theorem frame_ext (F G : FrameNorms K) (ha : F.arch=G.arch)
    (hfin : F.finiteNorm=G.finiteNorm) : F=G := by
  cases F
  cases G
  cases ha
  cases hfin
  rfl

/-- Scaling back the auxiliary finite-place norm by 210 cancels exactly,
including at 2,3,5,7. This computational identity is NOT a geometric KS map. -/
theorem cancel (H : FrameNorms K) :
    InducedLattice318.induced (comparisonFrame H) (210:K) (by norm_num) = InducedLattice318.square H := by
  apply frame_ext _ _ rfl
  funext w
  change (H.finiteNorm w)^2 / w.val ((210:K)⁻¹) / w.val 210 = (H.finiteNorm w)^2
  rw [map_inv₀,div_inv_eq_mul,mul_div_cancel_right₀ _ (w.val.pos (by norm_num : (210:K)≠0)).ne']

theorem comparison_degree (H : FrameNorms K) :
    (comparisonFrame H).normalizedDegree = 2*H.normalizedDegree+Real.log 210 :=
  InducedLattice318.ks_degree _ _ (cancel H)

/-- Sufficiency for the NUMERICAL height bound. All finite and infinite
estimates remain genuine hypotheses for the specified Hodge frame and
specified sections. It does not turn them into arithmetic theorems. -/
theorem height_from_local_hodge_inequalities (H : FrameNorms K) (hYuan : ℝ)
    (hdegree : H.normalizedDegree=hYuan) (u v : ℤ) (a₀ a₁ : K)
    (ha₀ : a₀≠0) (hrel : a₁=((32*((u:ℚ)/(v:ℚ)):ℚ):K)*a₀)
    (harch : ∀ (w : InfinitePlace K) (i : Fin 2),
      w (![a₀,a₁] i)*(H.arch w)^2 ≤ ContactMetricSections318.sectionBound)
    (hfinite : ∀ (w : FinitePlace K) (i : Fin 2), w ((210:K)*(![a₀,a₁] i))*(H.finiteNorm w)^2 ≤ 1) :
    ContactHeight318.pointHeight u v < 2*(hYuan-Real.log Real.pi)+120 := by
  apply ContactMetricSections318.contact_metric_from_sections u v a₀ a₁ ha₀ hrel
    (comparisonFrame H) (hYuan-Real.log Real.pi)
  · rw [comparison_degree,hdegree]; ring
  · exact harch
  · intro w i
    rw [comparison_finite]
    have h := hfinite w i
    rw [map_mul] at h
    calc
      _ = w (210:K)*w (![a₀,a₁] i)*(H.finiteNorm w)^2 := by ring
      _ ≤ 1 := h
end DirectHodgeSectionHeight318
