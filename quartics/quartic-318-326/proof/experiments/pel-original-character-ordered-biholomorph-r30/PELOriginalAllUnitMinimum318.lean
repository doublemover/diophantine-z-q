module
public import PELOriginalVertexEnergy318
public import PELPolygonAffineMinimum318
public import PELRealKleinSideTransport318
public section
noncomputable section
namespace PELOriginalAllUnitMinimum318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318
open PELJointNormOneAction318 QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELOriginalDirichletPolygon318 PELOriginalProjectiveTangents318
open PELRealProjectiveDifferential318
set_option maxHeartbeats 1800000

/-- The all-integer vertex theorem extends to EVERY real point of the
actual finite polygon through its exact 13 closed horizontal strips. -/
theorem whole_polygon_denominator (x : Coordinates) (hx : integerNorm x=1)
    (A B : ℝ) (hP : inequalities A B) :
    1 ≤ denominator (realMatrix (embed x)) (A,B) := by
  let M := realMatrix (embed x)
  change 1 ≤ (M *ᵥ ![A,B,1]) 2
  rw [← affineForm_value]
  apply PELPolygonAffineMinimum318.whole_polygon
    (M 2 0) (M 2 1) (M 2 2) A B hP
  intro v
  have hv : 1 ≤ denominator M (realPoint (PELDirichletSidePairingData318.vertex v)) := by
    dsimp [M]
    rw [denominator_cast]
    exact_mod_cast PELOriginalVertexEnergy318.vertex_minimum v x hx
  simpa only [denominator,← affineForm_value,affineForm,realPoint] using hv

/-- Every original norm-one unit, not just the 28 side units, increases
height at each point in the literal finite halfplane polygon. -/
theorem original_all_unit_minimum (τ : HalfPlane) (hτ : τ∈originalDomain)
    (u : normOneUnits) : height τ ≤ height (u • τ) := by
  obtain ⟨x,hx⟩ := (show ((u.val:order):B)∈order from (u.val:order).property)
  have hn : integerNorm x=1 := by
    have h := (mem_normOneUnits u.val).mp u.property
    rw [← hx,embed_norm] at h
    exact_mod_cast h
  have hd := whole_polygon_denominator x hn (scaledFirst τ) (scaledSecond τ) hτ
  rw [hx] at hd
  rw [PELRealKleinSideTransport318.original_height_multiplier]
  nlinarith [height_pos τ]

/-- Exact identification of the LITERAL 32-halfplane polygon with the
Dirichlet height-minimum set for the ENTIRE original arithmetic group.
This is not yet a local quotient chart or a polygon cellulation theorem. -/
theorem originalDomain_iff_all_units (τ : HalfPlane) :
    τ∈originalDomain ↔ ∀ u : normOneUnits,height τ ≤ height (u • τ) := by
  constructor
  · intro h u
    exact original_all_unit_minimum τ h u
  · intro h j ε δ
    exact PELDirichletOrbitBound318.signed_row τ h j ε δ

/-- Any two representatives from this polygon in one original orbit have
exactly the same height. This retains boundary identifications rather than
claiming uniqueness from a finite side table. -/
theorem polygon_orbit_height (τ : HalfPlane) (u : normOneUnits)
    (hτ : τ∈originalDomain) (huτ : u • τ∈originalDomain) :
    height (u • τ)=height τ := by
  apply le_antisymm
  · have h := original_all_unit_minimum (u • τ) huτ u⁻¹
    simpa only [inv_smul_smul] using h
  · exact original_all_unit_minimum τ hτ u
end PELOriginalAllUnitMinimum318
