module
public import FifthInfinityInvariantRestriction318
public import RegularUnitMultiple318
public section
noncomputable section
namespace FifthInfinityRegularMultiple318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open InfinityGlobalDifferentialRestriction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Every actual invariant global differential is a regular multiple of the
actual fifth invariant pullback on the entire infinity chart. The u factor
is removed by proved divisibility, never by dividing by u in that ring. -/
theorem form_multiple (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s):
    ∃a:I,form s=a • form FifthActualDifferential318.differential:=by
  obtain ⟨a,ha⟩:=invariant_factorization s h
  exact RegularUnitMultiple318.of_factorizations (K:=I) (V:=KaehlerDifferential ℚ I)
    (InfinityOrderCoordinates318.coordinate units) a FifthInfinityInvariantCoefficient318.factor
    (form s) (form FifthActualDifferential318.differential)
    (KaehlerDifferential.D ℚ I (InfinityOrderCoordinates318.coordinate units))
    FifthInfinityInvariantCoefficient318.factor_unit ha FifthInfinityInvariantRestriction318.normalized
/-- The same regular multiple equality as actual intrinsic sheaf sections,
with scalar supplied by the actual affine chart structure isomorphism. -/
theorem section_multiple (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s):
    ∃a:I,M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s=
      ScaledGlobalSectionRestriction318.scalar j a •
        M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op FifthActualDifferential318.differential:=by
  obtain ⟨a,ha⟩:=form_multiple s h
  refine ⟨a,?_⟩
  rw [←form_restrict,ha,IntrinsicChartSections318.section_smul,form_restrict]
  rfl
theorem average_section_multiple (s:Γ(M,⊤)):
    ∃a:I,M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
        (FifthDifferentialAveraging318.average s)=
      ScaledGlobalSectionRestriction318.scalar j a •
        M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op FifthActualDifferential318.differential:=
  section_multiple _ (FifthDifferentialInvariantSummand318.average_fixed s)
end FifthInfinityRegularMultiple318
