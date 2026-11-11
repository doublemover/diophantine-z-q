module
public import PELOriginalKleinHomeomorph318
public section
noncomputable section
namespace PELOriginalDirichletPolygon318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318 PELDirichletOriginalUnits318
open PELDirichletPolygonCertificate318 PELOriginalKleinHomeomorph318
open PELHeightCompactSublevels318 PELQuaternionRealRepresentation318
set_option maxHeartbeats 1800000

/-- The finite rational halfplane intersection in the EXACT scaled Klein
plane. Duplicate axis inequalities do not change this set. -/
@[expose] def inequalities (A B : ℝ) : Prop := ∀ (j : Fin 8) (ε δ : Bool),
  (rowFirst j:ℝ)*((sign ε:ℝ)*A)+(rowSecond j:ℝ)*((sign δ:ℝ)*B)≤(rowConstant j:ℝ)
@[expose] def planePolygon : Set (ℝ×ℝ) := {p | inequalities p.1 p.2}
@[expose] def originalDomain : Set HalfPlane := {τ | inequalities (scaledFirst τ) (scaledSecond τ)}

theorem radius_bound (A B : ℝ) (h : inequalities A B) : A^2/1050+B^2/5≤9999/10000 := by
  have habs (j : Fin 8) : (rowFirst j:ℝ)*|A|+(rowSecond j:ℝ)*|B|≤(rowConstant j:ℝ) := by
    apply absolute_halfplane
    intro ε δ hε hδ
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
    · simpa [sign] using h j false false
    · simpa [sign] using h j false true
    · simpa [sign] using h j true false
    · simpa [sign] using h j true true
  have h0 := habs 0
  have h1 := habs 1
  have h2 := habs 2
  have h3 := habs 3
  have h4 := habs 4
  have h5 := habs 5
  have h6 := habs 6
  have h7 := habs 7
  norm_num [rowFirst,rowSecond,rowConstant] at h0 h1 h2 h3 h4 h5 h6 h7
  have H := polygon_bound |A| |B| (abs_nonneg _) (abs_nonneg _)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  simpa only [sq_abs] using H

theorem scaled_continuous : Continuous (fun τ : HalfPlane => (scaledFirst τ,scaledSecond τ)) := by
  have h := continuous_subtype_val.comp continuous_toDisk
  exact (continuous_const.mul (continuous_fst.comp h)).prodMk
    (continuous_const.mul (continuous_snd.comp h))

theorem originalDomain_closed : IsClosed originalDomain := by
  have hA := continuous_fst.comp scaled_continuous
  have hB := continuous_snd.comp scaled_continuous
  change IsClosed {τ : HalfPlane | ∀ (j : Fin 8) (ε δ : Bool),
    (rowFirst j:ℝ)*((sign ε:ℝ)*scaledFirst τ)+
      (rowSecond j:ℝ)*((sign δ:ℝ)*scaledSecond τ)≤(rowConstant j:ℝ)}
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun j => isClosed_iInter (fun ε => isClosed_iInter (fun δ =>
    isClosed_le ((continuous_const.mul (continuous_const.mul hA)).add
      (continuous_const.mul (continuous_const.mul hB))) continuous_const)))

theorem domain_height (τ : HalfPlane) (hτ : τ∈originalDomain) : height τ≤200 := by
  have hr := radius_bound (scaledFirst τ) (scaledSecond τ) hτ
  have hid := disk_height_identity τ
  have hp := height_pos τ
  have hm := mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (height τ))
  nlinarith

theorem originalDomain_compact : IsCompact originalDomain :=
  (sublevel_compact 200 (by norm_num)).of_isClosed_subset originalDomain_closed domain_height

/-- Every original orbit meets this LITERAL finite polygon, not just the
coarser height bound. No claim that the representative is unique. -/
theorem original_polygon_reduction (τ : HalfPlane) :
    ∃ u : PELJointNormOneAction318.normOneUnits,u • τ∈originalDomain := by
  obtain ⟨u,hu⟩ := PELOriginalOrbitHeightMinimum318.original_minimum τ
  exact ⟨u,fun j ε δ => PELDirichletOrbitBound318.signed_row (u • τ) hu j ε δ⟩

/-- Literal scaled real coordinate map on the original compact polygon. -/
@[expose] def polygonCoordinate (τ : originalDomain) : planePolygon :=
  ⟨(scaledFirst τ.val,scaledSecond τ.val),τ.property⟩

theorem polygonCoordinate_injective : Function.Injective polygonCoordinate := by
  intro τ σ h
  have hA := congrArg (fun p : planePolygon => p.val.1) h
  have hB := congrArg (fun p : planePolygon => p.val.2) h
  apply Subtype.ext
  apply toDisk_injective
  apply Subtype.ext
  apply Prod.ext
  · exact mul_left_cancel₀ (mul_ne_zero alpha_pos.ne' beta_pos.ne') hA
  · exact mul_left_cancel₀ beta_pos.ne' hB
end PELOriginalDirichletPolygon318
