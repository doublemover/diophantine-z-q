module
public import CompletedFieldPoints318
public import RationalWeierstrassPoints318
public section
noncomputable section
namespace RationalCompletedPoints318
open CompletedFieldPoints318 RationalWeierstrassPoints318
variable {K:Type} [Field K] [Algebra ℚ K]
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2)))
include hD

/-- All actual field-valued points of the completed literal Scheme, including infinity,
identified with the genuine Mathlib Weierstrass point type. -/
@[expose] def fieldPointEquiv :
    CompletedFieldPoints318.SchemePoints (K:=K) A B ≃
      (RationalWeierstrassPoints318.model (K:=K) A B hD).Point := by
  classical
  exact (CompletedFieldPoints318.completedEquiv _ _).trans
    ((Equiv.optionCongr (RationalWeierstrassPoints318.fieldPointEquiv A B hD)).trans
      (Equiv.optionSubtypeNe WeierstrassCurve.Affine.Point.zero))

/-- The actual closed infinity section is the actual elliptic identity point. -/
theorem fieldPointEquiv_infinity : fieldPointEquiv (K:=K) A B hD
    (CompletedFieldPoints318.infinityPoint A B)=
      WeierstrassCurve.Affine.Point.zero := by
  classical
  simp [fieldPointEquiv]
  rfl

/-- On the original finite chart this is exactly the previously checked coordinate equivalence. -/
theorem fieldPointEquiv_finite
    (p : AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    fieldPointEquiv A B hD (CompletedFieldPoints318.finiteInclusion _ _ p)=
      (RationalWeierstrassPoints318.fieldPointEquiv A B hD p).val := by
  classical
  simp [fieldPointEquiv]
  rfl

/-- Exact literal coordinates, not an unspecified bijection of field-point sets. -/
theorem fieldPointEquiv_coordinates
    (p : AffineEquationFunctor318.Solutions (S:=K) A B) :
    fieldPointEquiv A B hD (CompletedFieldPoints318.finiteInclusion _ _
      ((AffineSchemeSolutions318.schemeSolutionEquiv _ _).symm p))=
    (RationalWeierstrassPoints318.solutionPoint (RationalWeierstrassPoints318.model A B hD)
      ⟨p.val,(RationalWeierstrassPoints318.solution_iff_equation A B hD p.val.1 p.val.2).mp p.property⟩).val := by
  rw [fieldPointEquiv_finite,RationalWeierstrassPoints318.fieldPointEquiv_coordinates]

end RationalCompletedPoints318
