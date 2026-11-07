module
public import DuplicationProjective318
public section
namespace RelativeDuplicationHeight318
open ConcreteG8Domain LocalGenerator318 DuplicationProjective318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

instance actual_number_field : NumberField K := {}

/-- The actual relative logarithmic height from the number field's finite
and infinite places. Dividing by degree gives the absolute normalization. -/
@[expose] def relativeXHeight (Q:E.Point) : ℝ := Height.logHeight Q.xRep

/-- Exact identity connecting the actual doubled elliptic point to the
homogeneous forms used by the checked archimedean and local gcd estimates.
It includes infinity and all 2-torsion cases. -/
theorem double_height_forms (Q:E.Point) :
    relativeXHeight ((2:ℤ) • Q)=Height.logHeight (forms Q) := by
  obtain ⟨s,hs,he⟩ := forms_represent_double Q
  rw [he,Height.logHeight_smul_eq_logHeight _ hs]
  rfl

theorem relative_height_nonneg (Q:E.Point) : 0≤relativeXHeight Q := Height.logHeight_nonneg _

theorem relative_height_neg (Q:E.Point) : relativeXHeight (-Q)=relativeXHeight Q := by
  simp [relativeXHeight,Point.xRep_neg]

end
end RelativeDuplicationHeight318
