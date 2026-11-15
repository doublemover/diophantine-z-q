module
public import PELOriginalOrbitHeightMinimum318
public section
noncomputable section
namespace PELDirichletOrbitBound318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318 PELDirichletOriginalUnits318
open PELDirichletPolygonCertificate318 PELOriginalOrbitHeightMinimum318 PELJointNormOneAction318
set_option maxHeartbeats 1800000

/-- Every signed row is forced by the corresponding actual integral unit,
not by a presumed full Dirichlet or fundamental polygon. -/
theorem signed_row (τ : HalfPlane) (hτ : ∀ u : normOneUnits,height τ≤height (u • τ))
    (j : Fin 8) (ε δ : Bool) :
    (rowFirst j:ℝ)*((sign ε:ℝ)*scaledFirst τ)+
      (rowSecond j:ℝ)*((sign δ:ℝ)*scaledSecond τ)≤(rowConstant j:ℝ) := by
  have hn : 0≤2*(height (testUnit j ε δ • τ)-height τ)/height τ :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hτ _))) (height_pos τ).le
  rw [original_energy] at hn
  linarith

theorem absolute_row (τ : HalfPlane) (hτ : ∀ u : normOneUnits,height τ≤height (u • τ))
    (j : Fin 8) :
    (rowFirst j:ℝ)*|scaledFirst τ|+(rowSecond j:ℝ)*|scaledSecond τ|≤(rowConstant j:ℝ) := by
  apply absolute_halfplane
  intro ε δ hε hδ
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
  · simpa [sign] using signed_row τ hτ j false false
  · simpa [sign] using signed_row τ hτ j false true
  · simpa [sign] using signed_row τ hτ j true false
  · simpa [sign] using signed_row τ hτ j true true

/-- An exact rational overdomain, not a claim that these finitely many
bisectors list every side of the full original-group Dirichlet domain. -/
theorem radius_bound (τ : HalfPlane) (hτ : ∀ u : normOneUnits,height τ≤height (u • τ)) :
    (scaledFirst τ)^2/1050+(scaledSecond τ)^2/5≤9999/10000 := by
  have h0 := absolute_row τ hτ 0
  have h1 := absolute_row τ hτ 1
  have h2 := absolute_row τ hτ 2
  have h3 := absolute_row τ hτ 3
  have h4 := absolute_row τ hτ 4
  have h5 := absolute_row τ hτ 5
  have h6 := absolute_row τ hτ 6
  have h7 := absolute_row τ hτ 7
  norm_num [rowFirst,rowSecond,rowConstant] at h0 h1 h2 h3 h4 h5 h6 h7
  have h := polygon_bound |scaledFirst τ| |scaledSecond τ| (abs_nonneg _) (abs_nonneg _)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  simpa only [sq_abs] using h

theorem minimum_height_bound (τ : HalfPlane)
    (hτ : ∀ u : normOneUnits,height τ≤height (u • τ)) : height τ≤200 := by
  have hr := radius_bound τ hτ
  have hid := disk_height_identity τ
  have hp := height_pos τ
  have hmul := mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (height τ))
  nlinarith

/-- Full original orbit coverage by ONE fixed compact height sublevel. -/
theorem original_orbit_reduction (τ : HalfPlane) :
    ∃ u : normOneUnits,height (u • τ)≤200 := by
  obtain ⟨u,hu⟩ := original_minimum τ
  exact ⟨u,minimum_height_bound (u • τ) hu⟩
end PELDirichletOrbitBound318
