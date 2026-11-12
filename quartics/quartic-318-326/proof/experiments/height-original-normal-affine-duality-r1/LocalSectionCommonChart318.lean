module
public import ActualCommonLocalPoint318
public section
noncomputable section
namespace LocalSectionCommonChart318
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {g : Spec (CommRingCat.of R) ⟶ X}
  (A B : LocalSectionAffineChart318.Data f g)

/-- The common neighborhood carries the WHOLE original section, not
only its generic point or closed image. Both evaluations remain literal. -/
abbrev Common := ActualCommonLocalPoint318.Data
  A.inclusion B.inclusion A.evaluation B.evaluation

theorem exists_common : Nonempty (Common A B) := by
  letI := A.openImmersion
  letI := B.openImmersion
  exact ActualCommonLocalPoint318.exists_data _ _ _ _
    (A.section_eq.trans B.section_eq.symm)

@[expose] def common : Common A B := Classical.choice (exists_common A B)

variable (C : Common A B)

lemma scalar_square : A.scalar ≫ C.left = B.scalar ≫ C.right :=
  C.scalar_square f A.scalar B.scalar A.over_base B.over_base

/-- The common integral evaluation is a retraction of the SAME base
scalar, with no fraction-field localization or assumed chart regularity. -/
lemma scalar_retraction : (A.scalar ≫ C.left) ≫ C.evaluation = 𝟙 _ := by
  rw [Category.assoc,C.left_point,A.retraction]
end LocalSectionCommonChart318
