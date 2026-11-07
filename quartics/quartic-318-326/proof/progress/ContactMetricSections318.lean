module
public import RationalSectionHeight318
public import FiveContactProducer318
public section
noncomputable section
namespace ContactMetricSections318
open NumberField Height SectionHeight318 FiveContactProducer318 ContactHeight318
set_option maxHeartbeats 0

/-- Actual bound for the integral sections J²q0 and J²q1. -/
@[expose] def sectionBound : ℝ := 2765952000^2*(4*12540153541944538512)

theorem sectionBound_log : Real.log sectionBound =
    2*Real.log 2765952000+Real.log (4*12540153541944538512) := by
  unfold sectionBound
  rw [Real.log_mul (by norm_num : (2765952000:ℝ)^2≠0)
    (by norm_num : (4*12540153541944538512:ℝ)≠0),Real.log_pow]
  norm_num

/-- The exact metric rescaling loss, using actual rational height. -/
theorem rational_scale_loss (q:ℚ) :
    Height.logHeight₁ q≤Height.logHeight₁ (32*q)+Real.log 32 := by
  have h:=Height.logHeight₁_mul_le (32*q) ((1:ℚ)/32)
  have he:(32*q)*((1:ℚ)/32)=q := by ring
  rw [he] at h
  have hc:Height.logHeight₁ ((1:ℚ)/32)=Real.log 32 := by
    norm_num [Rat.logHeight₁_eq_log_max]
  rwa [hc] at h

/-- Derive the actual contact-metric inequality from genuine NumberField
section norms and the exact Yuan/Hodge normalized-degree identification.
No contact-height inequality is supplied as a premise. -/
theorem contact_metric_from_sections {K:Type*} [Field K] [NumberField K]
    (u v:ℤ) (a₀ a₁:K) (ha₀:a₀≠0)
    (hrel:a₁=((32*((u:ℚ)/(v:ℚ)):ℚ):K)*a₀)
    (F:FrameNorms K) (hOriginal:ℝ)
    (hdegree:F.normalizedDegree=2*(hOriginal+Real.log Real.pi)+Real.log 210)
    (harch:∀(w:InfinitePlace K) i,w (![a₀,a₁] i)*F.arch w≤sectionBound)
    (hfinite:∀(w:FinitePlace K) i,w (![a₀,a₁] i)*F.finiteNorm w≤1) :
    pointHeight u v<2*hOriginal+120 := by
  have hsec:=rational_section_height a₀ a₁ (32*((u:ℚ)/(v:ℚ))) ha₀ hrel
    F sectionBound harch hfinite
  have hscale:=rational_scale_loss ((u:ℚ)/(v:ℚ))
  rw [hdegree,sectionBound_log] at hsec
  have hbudget:=MetricCancellation318.geometric_additive_lt_120
  rw [pointHeight_eq_contact_height,DetectorHeightTransfer318.rational_height_eq]
  calc
    _ ≤ Height.logHeight₁ (32*((u:ℚ)/(v:ℚ)))+Real.log 32 := hscale
    _ ≤ (2*(hOriginal+Real.log Real.pi)+Real.log 210+
      (2*Real.log 2765952000+Real.log (4*12540153541944538512)))+Real.log 32 :=
        add_le_add hsec (le_refl _)
    _ < 2*hOriginal+120 := by
      convert add_lt_add_left hbudget (2*hOriginal) using 1 <;> ring

/-- A larger shifted surface height preserves the actual source comparison. -/
theorem contact_metric_shifted {K:Type*} [Field K] [NumberField K]
    (u v:ℤ) (a₀ a₁:K) (ha₀:a₀≠0)
    (hrel:a₁=((32*((u:ℚ)/(v:ℚ)):ℚ):K)*a₀)
    (F:FrameNorms K) (hOriginal hShifted:ℝ)
    (hdegree:F.normalizedDegree=2*(hOriginal+Real.log Real.pi)+Real.log 210)
    (hshift:hShifted=hOriginal+Real.log Real.pi)
    (harch:∀(w:InfinitePlace K) i,w (![a₀,a₁] i)*F.arch w≤sectionBound)
    (hfinite:∀(w:FinitePlace K) i,w (![a₀,a₁] i)*F.finiteNorm w≤1) :
    pointHeight u v≤2*hShifted+120 := by
  have h:=contact_metric_from_sections u v a₀ a₁ ha₀ hrel F hOriginal hdegree harch hfinite
  have hp:0≤Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [hshift]
  linarith

end ContactMetricSections318
