module
public import ActualTwoDescentOriginalGeometricLiftGroupPairing318
public section
noncomputable section
namespace ActualTwoDescentFractionalLineStabilizerRegularity318
open ActualTwoDescentNativeFractionalIdealImage318 ActualTwoDescentFractionalLineScaling318
variable {R F : Type*} [CommRing R] [Field F] [Algebra R F]
/-- Full preservation of one NONZERO fractional principal lattice
forces BOTH multiplier and inverse to be regular. No DVR hypothesis. -/
lemma regular (w : F) (hw : w≠0) (a : Fˣ)
    (h : ∀ f,f∈line (R:=R) w ↔ (a:F)*f∈line (R:=R) w) :
    (∃ r : R,algebraMap R F r=(a:F)) ∧
      (∃ r : R,algebraMap R F r=(↑a⁻¹:F)) := by
  have hm : w∈line (R:=R) w := ⟨1,by simp⟩
  constructor
  · obtain ⟨r,hr⟩ := (h w).mp hm
    exact ⟨r,mul_right_cancel₀ hw hr⟩
  · have hi : (↑a⁻¹:F)*w∈line (R:=R) w := by
      apply (h _).mpr
      simpa [←mul_assoc] using hm
    obtain ⟨r,hr⟩ := hi
    exact ⟨r,mul_right_cancel₀ hw hr⟩
/-- Conversely every actual stalk unit preserves the entire fractional
line. The statement keeps the literal stalk-to-field map. -/
lemma unit_preserves (w : F) (u : Rˣ) (f : F) :
    f∈line (R:=R) w ↔ algebraMap R F (u:R)*f∈line (R:=R) w := by
  have hu : algebraMap R F (u:R)≠0 := (u.isUnit.map (algebraMap R F)).ne_zero
  rw [scale_mem (R:=R) (algebraMap R F (u:R)) w f hu,line_unit_mul]

end ActualTwoDescentFractionalLineStabilizerRegularity318
