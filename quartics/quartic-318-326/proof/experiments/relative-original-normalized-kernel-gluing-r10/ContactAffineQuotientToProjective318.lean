module
public import ContactRelativeLinearOpenChart318
public import VaryingProjectiveQuotientFamily318
public import FiniteClosedInOpen318
public section
noncomputable section
namespace ContactAffineQuotientToProjective318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingProjectiveQuotientEquiv318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ)
  (l : MvPolynomial (Fin 2) ℚ) (hl : l∈ProjectiveJLine318.grading ℚ 1)
  (n : ℕ)
local notation "A" => ContactOriginalLinearOpenChart318.ring c l hl
variable (I : ProjectiveIdeal ℚ A (Fin n) S)
abbrev family := VaryingWholeIdealFamily318.family ℚ A S I.val
/-- The SAME literal finite-projective affine quotient is inserted in
the original projective source, rather than a detached affine model. -/
@[expose] def into : family S c l hl n I ⟶ ContactRelativeLinearOpenChart318.curve S c :=
  VaryingWholeIdealFamily318.into ℚ A S I.val ≫ ContactRelativeLinearOpenChart318.into S c l hl
abbrev projection := VaryingWholeIdealFamily318.projection ℚ A S I.val
@[reassoc] lemma into_projection : into S c l hl n I ≫ ContactRelativeLinearOpenChart318.projection S c=
    projection S c l hl n I := by
  rw [into,Category.assoc,ContactRelativeLinearOpenChart318.over_test]
  rfl
instance finite : IsFinite (projection S c l hl n I) :=
  VaryingLocalFreeFamilyRecovery318.finite ℚ A (Fin n) S (toLocal ℚ A (Fin n) S I)
instance flat : Flat (projection S c l hl n I) :=
  VaryingLocalFreeFamilyRecovery318.flat ℚ A (Fin n) S (toLocal ℚ A (Fin n) S I)
/-- Finiteness of the WHOLE quotient and separatedness of the source
upgrade the actual locally closed insertion to a global closed immersion. -/
instance closed : IsClosedImmersion (into S c l hl n I) := by
  letI : IsFinite ((VaryingWholeIdealFamily318.into ℚ A S I.val ≫
      ContactRelativeLinearOpenChart318.into S c l hl) ≫ ContactRelativeLinearOpenChart318.projection S c) := by
    change IsFinite (into S c l hl n I ≫ ContactRelativeLinearOpenChart318.projection S c)
    rw [into_projection]
    infer_instance
  exact FiniteClosedInOpen318.closed (VaryingWholeIdealFamily318.into ℚ A S I.val)
    (ContactRelativeLinearOpenChart318.into S c l hl) (ContactRelativeLinearOpenChart318.projection S c)
end ContactAffineQuotientToProjective318
