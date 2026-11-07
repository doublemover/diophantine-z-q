module
public import IsogenyHeightTransfer318
public import MetricCancellation318
public section
noncomputable section
namespace CMSurfaceTransfer318
open ActualLogWeight318 IsogenyHeightTransfer318

/-- The inherited854R estimate concerns the CM surface. The geometric comparison doubles it. -/
theorem actual_CM_contact_bound (R hSurface hContact:ℝ) (hR:1≤R)
    (hCM:hSurface<854*R) (hGeometric:hContact≤2*hSurface+120) :
    hContact<2^68*C^2*R^((49:ℝ)/8)+128 := by
  obtain ⟨hr1,hr,he⟩:=source_exponent_bounds R hR
  have hc:=one_le_C_sq
  have hm:=mul_le_mul_of_nonneg_right hc (show 0≤R^((49:ℝ)/8) by positivity)
  nlinarith

theorem surface_normalization_bound (hOriginal hShifted:ℝ)
    (hShift:hShifted=hOriginal+Real.log Real.pi) : hShifted<hOriginal+2 := by
  have h:=MetricCancellation318.normalization_log_bound
  rw [Real.log_sqrt Real.pi_pos.le] at h
  rw [hShift]
  linarith

/-- The exact dimension-two normalization shift also fits the source cap. -/
theorem actual_CM_shifted_contact_bound (R hOriginal hShifted hContact:ℝ) (hR:1≤R)
    (hCM:hOriginal<854*R) (hShift:hShifted=hOriginal+Real.log Real.pi)
    (hGeometric:hContact≤2*hShifted+120) :
    hContact<2^68*C^2*R^((49:ℝ)/8)+128 := by
  have hShiftb:=surface_normalization_bound hOriginal hShifted hShift
  obtain ⟨hr1,hr,he⟩:=source_exponent_bounds R hR
  have hc:=one_le_C_sq
  have hm:=mul_le_mul_of_nonneg_right hc (show 0≤R^((49:ℝ)/8) by positivity)
  nlinarith
end CMSurfaceTransfer318
#print axioms CMSurfaceTransfer318.actual_CM_contact_bound
#print axioms CMSurfaceTransfer318.actual_CM_shifted_contact_bound

#print axioms CMSurfaceTransfer318.surface_normalization_bound
