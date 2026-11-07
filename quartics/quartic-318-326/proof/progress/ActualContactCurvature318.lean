module
public import GradientNorm318
public section
noncomputable section
open Finset
namespace ActualContactCurvature318
set_option maxHeartbeats 0

@[expose] def x (z:ℂ) (i:Fin 4) : ℝ := (z-FiveContactMetricBounds318.contact i).re
@[expose] def y (z:ℂ) (i:Fin 4) : ℝ := (z-FiveContactMetricBounds318.contact i).im
@[expose] def localCoefficient (z:ℂ) : (ℝ×ℝ)→ℝ := ContactCurvature318.metric (x z) (y z)
@[expose] def coefficient (z:ℂ) : ℝ := FiveContactMetricBounds318.U z /
  ∏i:Fin 4,FiveContactMetricBounds318.radius z i

/-- These are the actual source's scaled contact distances. -/
theorem radius_eq (z:ℂ) (i:Fin 4) : DistanceLaplacian318.radius (x z i) (y z i)=
    FiveContactMetricBounds318.radius z i := by
  rw [x,y,DistanceLaplacian318.radius_complex]
  simp only [FiveContactMetricBounds318.radius,dist_eq_norm]

theorem offsets_positive (z:ℂ) (hz:∀i:Fin 4,z≠FiveContactMetricBounds318.contact i) :
    ∀i:Fin 4,0<(x z i)^2+(y z i)^2 := by
  intro i
  have hn:0<‖z-FiveContactMetricBounds318.contact i‖:=norm_pos_iff.mpr (sub_ne_zero.mpr (hz i))
  have hs:=Complex.sq_norm (z-FiveContactMetricBounds318.contact i)
  simp only [Complex.normSq_apply] at hs
  dsimp only [x,y]
  nlinarith

theorem total_eq (z:ℂ) : ContactCurvature318.total (x z) (y z) (0,0)=
    FiveContactMetricBounds318.U z := by
  simp only [ContactCurvature318.total,DistanceLaplacian318.translated,add_zero,radius_eq,
    FiveContactMetricBounds318.U]

theorem translated_eq (z:ℂ) (w:ℝ×ℝ) (i:Fin 4) :
    DistanceLaplacian318.translated (x z i) (y z i) w=
      FiveContactMetricBounds318.radius (z+(⟨w.1,w.2⟩:ℂ)) i := by
  have he : (x z i+w.1)=(z+(⟨w.1,w.2⟩:ℂ)-FiveContactMetricBounds318.contact i).re ∧
      (y z i+w.2)=(z+(⟨w.1,w.2⟩:ℂ)-FiveContactMetricBounds318.contact i).im := by
    simp only [x,y,Complex.sub_re,Complex.add_re,Complex.sub_im,Complex.add_im]
    constructor <;> ring
  rw [DistanceLaplacian318.translated,he.1,he.2,DistanceLaplacian318.radius_complex]
  simp only [FiveContactMetricBounds318.radius,dist_eq_norm]

/-- The local coefficient is a genuine translation of the source metric,
not an independently prescribed curvature expression. -/
theorem localCoefficient_eq (z:ℂ) (w:ℝ×ℝ) :
    localCoefficient z w=coefficient (z+(⟨w.1,w.2⟩:ℂ)) := by
  simp only [localCoefficient,ContactCurvature318.metric,ContactCurvature318.total,
    ContactCurvature318.product,translated_eq,coefficient,FiveContactMetricBounds318.U]

theorem coefficient_pos (z:ℂ) (hz:∀i:Fin 4,z≠FiveContactMetricBounds318.contact i) :
    0<coefficient z := by
  exact div_pos (FiveContactMetricBounds318.U_pos z)
    (Finset.prod_pos (fun i _=>dist_pos.mpr (hz i)))

theorem localCoefficient_axisC2 (z:ℂ) (hz:∀i:Fin 4,z≠FiveContactMetricBounds318.contact i) :
    ConformalCurvature318.AxisC2 (localCoefficient z) :=
  ContactCurvature318.metric_axisC2 (x z) (y z) (offsets_positive z hz)

/-- Actual off-branch curvature bound for the literal four-distance metric. -/
theorem curvature_bound (z:ℂ) (hz:∀i:Fin 4,z≠FiveContactMetricBounds318.contact i) :
    ConformalCurvature318.curvature (localCoefficient z) ≤
      -(12540153541944538512:ℝ)⁻¹ := by
  have hl:=GradientNorm318.curvature_lower (x z) (y z) (offsets_positive z hz)
  simp only [radius_eq,total_eq] at hl
  have hg:=FiveContactMetricBounds318.global_curvature_ratio_bound z
  change ConformalCurvature318.curvature (ContactCurvature318.metric (x z) (y z))≤_
  linarith

end ActualContactCurvature318
#print axioms ActualContactCurvature318.curvature_bound
