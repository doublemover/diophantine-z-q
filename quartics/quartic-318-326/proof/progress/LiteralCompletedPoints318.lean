module
public import CompletedFieldPoints318
public section
noncomputable section
namespace LiteralCompletedPoints318
open CompletedFieldPoints318 LiteralWeierstrassPoints318
variable {K : Type} [Field K] (N : ℕ) [Algebra (OpenJModel318.Base N) K]

/-- All actual field-valued points of the completed literal Scheme, including infinity,
identified with the genuine Mathlib Weierstrass point type. -/
@[expose] def fieldPointEquiv :
    CompletedFieldPoints318.SchemePoints (K:=K) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≃
      (LiteralWeierstrassPoints318.model (K:=K) N).Point := by
  classical
  exact (CompletedFieldPoints318.completedEquiv _ _).trans
    ((Equiv.optionCongr (LiteralWeierstrassPoints318.fieldPointEquiv N)).trans
      (Equiv.optionSubtypeNe WeierstrassCurve.Affine.Point.zero))

/-- The actual closed infinity section is the actual elliptic identity point. -/
theorem fieldPointEquiv_infinity : fieldPointEquiv (K:=K) N
    (CompletedFieldPoints318.infinityPoint (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))=
      WeierstrassCurve.Affine.Point.zero := by
  classical
  simp [fieldPointEquiv]
  rfl

/-- On the original finite chart this is exactly the previously checked coordinate equivalence. -/
theorem fieldPointEquiv_finite
    (p : AffineSchemeSolutions318.SchemePoints (K:=K) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) :
    fieldPointEquiv N (CompletedFieldPoints318.finiteInclusion _ _ p)=
      (LiteralWeierstrassPoints318.fieldPointEquiv N p).val := by
  classical
  simp [fieldPointEquiv]
  rfl

/-- Exact literal coordinates, not an unspecified bijection of field-point sets. -/
theorem fieldPointEquiv_coordinates
    (p : AffineEquationFunctor318.Solutions (S:=K) (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) :
    fieldPointEquiv N (CompletedFieldPoints318.finiteInclusion _ _
      ((AffineSchemeSolutions318.schemeSolutionEquiv _ _).symm p))=
    (LiteralWeierstrassPoints318.solutionPoint (LiteralWeierstrassPoints318.model N)
      ⟨p.val,(LiteralWeierstrassPoints318.solution_iff_equation N p.val.1 p.val.2).mp p.property⟩).val := by
  rw [fieldPointEquiv_finite,LiteralWeierstrassPoints318.fieldPointEquiv_coordinates]

end LiteralCompletedPoints318
