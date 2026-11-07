module
public import ActualContactCurvature318
public import LiteralMetricExtension318
public section
noncomputable section
namespace LiteralCurvature318
open ActualContactCurvature318

/-- The literal off-branch and completed-branch packets use identical contacts. -/
theorem contacts_eq : FiveContactMetricBounds318.contact=LiteralMetricExtension318.contacts := rfl

theorem coefficient_eq (z:ℂ) : coefficient z =
    MetricPullback318.sourceCoefficient LiteralMetricExtension318.contacts z := by
  simp only [coefficient,FiveContactMetricBounds318.U,FiveContactMetricBounds318.radius,
    dist_eq_norm,contacts_eq,MetricPullback318.sourceCoefficient]

theorem localCoefficient_eq (z:ℂ) : ActualContactCurvature318.localCoefficient z=
    (fun w:ℝ×ℝ=>MetricPullback318.sourceCoefficient LiteralMetricExtension318.contacts
      (z+((w.1:ℂ)+w.2*Complex.I))) := by
  funext w
  rw [ActualContactCurvature318.localCoefficient_eq,coefficient_eq]
  congr 2
  apply Complex.ext <;> simp

/-- Actual curvature bound in exactly the same chart convention as the
smooth branch/infinity extensions and compact comparison. -/
theorem literal_curvature_bound (z:ℂ) (hz:∀i:Fin 4,z≠LiteralMetricExtension318.contacts i) :
    ConformalCurvature318.curvature
      (fun w:ℝ×ℝ=>MetricPullback318.sourceCoefficient LiteralMetricExtension318.contacts
        (z+((w.1:ℂ)+w.2*Complex.I)))≤-(12540153541944538512:ℝ)⁻¹ := by
  rw [←localCoefficient_eq]
  exact curvature_bound z (by simpa only [contacts_eq] using hz)

theorem literal_axisC2 (z:ℂ) (hz:∀i:Fin 4,z≠LiteralMetricExtension318.contacts i) :
    ConformalCurvature318.AxisC2
      (fun w:ℝ×ℝ=>MetricPullback318.sourceCoefficient LiteralMetricExtension318.contacts
        (z+((w.1:ℂ)+w.2*Complex.I))) := by
  rw [←localCoefficient_eq]
  exact localCoefficient_axisC2 z (by simpa only [contacts_eq] using hz)

theorem literal_positive (z:ℂ) (hz:∀i:Fin 4,z≠LiteralMetricExtension318.contacts i) :
    0<MetricPullback318.sourceCoefficient LiteralMetricExtension318.contacts z := by
  rw [←coefficient_eq]
  exact coefficient_pos z (by simpa only [contacts_eq] using hz)
end LiteralCurvature318
#print axioms LiteralCurvature318.literal_curvature_bound
