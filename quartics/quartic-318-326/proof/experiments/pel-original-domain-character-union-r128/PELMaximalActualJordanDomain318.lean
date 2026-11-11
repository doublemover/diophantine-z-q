module
public import PELMaximalActualComplexDomain318
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public section
noncomputable section
namespace PELMaximalActualJordanDomain318
open Set Metric
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonCoordinates318
open PELMaximalHalfOctagonOriginalPoints318 PELMaximalHalfOctagonShape318
open PELMaximalHalfOctagonBoundary318 PELMaximalHalfOctagonSphere318
set_option maxHeartbeats 2400000

/-- The actual complex open domain is exactly the open part of the
constructed closed disk. This does not declare its radial parameter
holomorphic. -/
theorem openDomain_iff_disk_interior (z : closedDomain) :
    z.val∈openDomain ↔ ‖(actualClosedDisk z).val‖<1 := by
  obtain ⟨P,rfl⟩ := point_bijective.2 z
  have hd : actualClosedDisk (point P)=upperCutDisk P := by
    change upperCutDisk (cutComplexHomeomorph.symm (cutComplexHomeomorph P))=upperCutDisk P
    rw [Homeomorph.symm_apply_apply]
  rw [hd]
  have hz : 0<(cutPoint P:ℂ).im := (cutPoint P).property
  have hnorm := normalized_boundary_iff (upperCutCenter P)
  have hf : (upperCutCenter P).val∈frontier centeredPolygon ↔
      (upperCutCenter P).val∉strictPolygon := by
    rw [←closure_sdiff_interior,polygon_closed.closure_eq,interior_eq_strict]
    exact and_iff_right (upperCutCenter P).property
  rw [hf] at hnorm
  have hbound := ReflectedDiskJoukowski318.disk_bound (upperCutDisk P)
  change (0<(cutPoint P:ℂ).im ∧
    centerHomeomorph (PELMaximalActualComplexDomain318.coordinates (cutPoint P))∈strictPolygon) ↔ _
  rw [coordinates_halfPlane,cutPoint_coordinates]
  simp only [hz,true_and]
  change (upperCutCenter P).val∈strictPolygon ↔ ‖(upperCutDisk P).val‖<1
  constructor
  · intro h
    apply lt_of_le_of_ne hbound
    intro he
    exact (hnorm.mp he) h
  · intro h
    by_contra hn
    have he := hnorm.mpr hn
    change ‖(upperCutDisk P).val‖=1 at he
    linarith

@[expose] def closedOfOpen (z : openDomain) : closedDomain := ⟨z.val,openDomain_subset z.property⟩
@[expose] def closedOfBall (z : ball (0:ℂ) 1) : ReflectedDiskJoukowski318.Disk :=
  ⟨z.val,ball_subset_closedBall z.property⟩

theorem closedOfOpen_continuous : Continuous closedOfOpen := continuous_subtype_val.subtype_mk _
theorem closedOfBall_continuous : Continuous closedOfBall := continuous_subtype_val.subtype_mk _

/-- Actual original complex domain as an open disk, with the unchanged
ambient complex topology on its source. -/
@[expose] def actualOpenDisk : openDomain ≃ₜ ball (0:ℂ) 1 where
  toFun z := ⟨(actualClosedDisk (closedOfOpen z)).val,by
    simpa only [Metric.mem_ball,dist_zero_right] using
      (openDomain_iff_disk_interior (closedOfOpen z)).mp z.property⟩
  invFun z := ⟨(actualClosedDisk.symm (closedOfBall z)).val,by
    apply (openDomain_iff_disk_interior _).mpr
    rw [Homeomorph.apply_symm_apply]
    simpa only [Metric.mem_ball,dist_zero_right] using z.property⟩
  left_inv z := by
    apply Subtype.ext
    change (actualClosedDisk.symm (actualClosedDisk (closedOfOpen z))).val=z.val
    rw [Homeomorph.symm_apply_apply]
    rfl
  right_inv z := by
    apply Subtype.ext
    change (actualClosedDisk (actualClosedDisk.symm (closedOfBall z))).val=z.val
    rw [Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun :=
    (continuous_subtype_val.comp (actualClosedDisk.continuous.comp closedOfOpen_continuous)).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp (actualClosedDisk.symm.continuous.comp closedOfBall_continuous)).subtype_mk _

/-- The simply-connected input for a genuine Riemann mapping theorem is
constructed on the actual original complex domain, not on a substituted
level-three j-map parameter. -/
theorem actual_domain_simply_connected : IsSimplyConnected openDomain := by
  letI : ContractibleSpace (ball (0:ℂ) 1) :=
    (convex_ball (0:ℂ) 1).contractibleSpace ⟨0,by simp⟩
  letI : ContractibleSpace openDomain := actualOpenDisk.contractibleSpace_iff.mpr inferInstance
  exact inferInstance

theorem actual_domain_nonempty : openDomain.Nonempty := actual_domain_simply_connected.nonempty

theorem actual_domain_bounded : Bornology.IsBounded openDomain :=
  closedDomain_compact.isBounded.subset openDomain_subset

/-- All domain prerequisites are produced. This does not include a
conformal map, continuous boundary extension, Schwarz reflection, or an
analytic P1 theorem; those are distinct remaining analytic constructions. -/
theorem actual_riemann_mapping_domain : IsOpen openDomain ∧ IsSimplyConnected openDomain ∧
    openDomain≠Set.univ ∧ openDomain.Nonempty ∧ Bornology.IsBounded openDomain :=
  ⟨openDomain_open,actual_domain_simply_connected,openDomain_ne_univ,
    actual_domain_nonempty,actual_domain_bounded⟩
end PELMaximalActualJordanDomain318
