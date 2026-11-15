module
public import ContactBranchPoint318
public import IntrinsicTensorFrameValue318
public import ContactBicanonicalSectionRatios318
public section
noncomputable section
namespace ContactBicanonicalPointValue318
open AlgebraicGeometry CategoryTheory Opposite Polynomial
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i, RationalContactPoint318.parameters c t i ≠ 0)

/-- The scalar coefficient of an actual global bicanonical section in the
original branch-coordinate frame, evaluated at the original field point. -/
@[expose] def value (i : Fin 4) (q : Γ(ContactGlobalBicanonical318.tensor c, ⊤)) :
    RationalContactPoint318.PointField c t :=
  IntrinsicTensorFrameValue318.sectionValue
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (ContactBranchPoint318.branchPoint c t hn i)
    ((ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤ ≤ ⊤ from le_top)).op q)

/-- Exact evaluation of the already glued global q0, not a separately
chosen scalar with the desired nonvanishing property. -/
theorem value_q0 (i : Fin 4) :
    value c t hn i (ContactGlobalBicanonical318.q0 c) =
      ContactBranchPoint318.branchPoint c t hn i (ContactBicanonicalCoefficients318.branchQ0 c i) := by
  let ev := IntrinsicTensorFrameValue318.sectionValue
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (ContactBranchPoint318.branchPoint c t hn i)
  exact (congrArg ev (ContactGlobalBicanonical318.q0_restrict c (some i))).trans
    (IntrinsicTensorFrameValue318.sectionValue_weighted
      (ContactIntrinsicFrames318.branchEmbedding c i)
      (ContactIntrinsicDifferentials318.structureMap c)
      (ContactIntrinsicFrames318.branch_structure c i)
      (ContactDifferentialFrames318.sourceLocalizationFrame c i)
      (ContactBranchPoint318.branchPoint c t hn i)
      (ContactFrameNormalization318.sourceCoordinate c i)
      (ContactBicanonicalCoefficients318.branchQ0 c i)
      (ContactFrameNormalization318.source_coordinate_normalized c i))

theorem value_q1 (i : Fin 4) :
    value c t hn i (ContactGlobalBicanonical318.q1 c) =
      ContactBranchPoint318.branchPoint c t hn i (ContactBicanonicalCoefficients318.branchQ1 c i) := by
  let ev := IntrinsicTensorFrameValue318.sectionValue
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (ContactBranchPoint318.branchPoint c t hn i)
  exact (congrArg ev (ContactGlobalBicanonical318.q1_restrict c (some i))).trans
    (IntrinsicTensorFrameValue318.sectionValue_weighted
      (ContactIntrinsicFrames318.branchEmbedding c i)
      (ContactIntrinsicDifferentials318.structureMap c)
      (ContactIntrinsicFrames318.branch_structure c i)
      (ContactDifferentialFrames318.sourceLocalizationFrame c i)
      (ContactBranchPoint318.branchPoint c t hn i)
      (ContactFrameNormalization318.sourceCoordinate c i)
      (ContactBicanonicalCoefficients318.branchQ1 c i)
      (ContactFrameNormalization318.source_coordinate_normalized c i))

/-- q0 is nonzero in each original finite branch frame at this exact point. -/
theorem value_q0_ne (i : Fin 4) :
    value c t hn i (ContactGlobalBicanonical318.q0 c) ≠ 0 := by
  rw [value_q0 c t hn i]
  exact ((ContactBicanonicalCoefficients318.branchQ0_unit c i).map
    (ContactBranchPoint318.branchPoint c t hn i)).ne_zero

/-- The original rational contact coordinate is the ratio of the actual
section values, with the genuine point and frame maps retained. -/
theorem value_ratio (i : Fin 4) :
    value c t hn i (ContactGlobalBicanonical318.q1 c) =
      algebraMap ℚ (RationalContactPoint318.PointField c t) t *
        value c t hn i (ContactGlobalBicanonical318.q0 c) := by
  rw [value_q1 c t hn i, value_q0 c t hn i, ContactBicanonicalCoefficients318.branchQ1, map_mul]
  congr 1
  change ContactBranchPoint318.branchPoint c t hn i
    (algebraMap (ContactKummerOrder318.SourceOrder c) (ContactIntrinsicFrames318.BranchRing c i)
      (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) Polynomial.X)) = _
  rw [ContactBranchPoint318.branchPoint_polynomial]
  simp

/-- Literal five-form specialization of the two actual global section
values. This supplies only the scalar part of MetricSections; no metric,
Hodge norm, KS comparison or integrality bound is asserted. -/
theorem original_contact_sections (u v : ℤ)
    (hf : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    let t := 32 * ((u : ℚ) / (v : ℚ))
    let hn := RationalContactPoint318.parameters_ne_of_forms c u v hf
    value c t hn i (ContactGlobalBicanonical318.q0 c) ≠ 0 ∧
      value c t hn i (ContactGlobalBicanonical318.q1 c) =
        algebraMap ℚ (RationalContactPoint318.PointField c t) t *
          value c t hn i (ContactGlobalBicanonical318.q0 c) :=
  ⟨value_q0_ne c _ _ i, value_ratio c _ _ i⟩
end ContactBicanonicalPointValue318
