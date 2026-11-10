module
public import ComplexProjectiveSchemePoint318
public import ReducedSchemePointFactorization318
public import PELOriginalProjectiveCandidatePoints318
public import Mathlib.AlgebraicGeometry.Noetherian
public section
noncomputable section
namespace PELOriginalCandidateComplexPoints318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalProjectiveCandidatePoints318
open PELOriginalAllLevelProjectiveMap318 PELOriginalPolarizationTransitions318
open ComplexProjectiveSchemePoint318
variable (τ:ℂ)(hτ:0<τ.im)
local instance standardGrading:GradedAlgebra degrees:=MvPolynomial.gradedAlgebra

/-- Same original nine coordinates, now as a genuine Spec(C)-valued
point of the actual projective Scheme. -/
@[expose] def ambientPoint(q:Base τ):ComplexPoint⟶ambient:=
  ComplexProjectiveSchemePoint318.point (baseVector τ hτ 1 q)
    (actual_coordinate_nonzero τ hτ q)
lemma ambientPoint_underlying(q:Base τ)(x:ComplexPoint):
    ambientPoint τ hτ q x=originalPoint τ hτ q:=
  ComplexProjectiveSchemePoint318.underlying_point _ _ x
lemma ambientPoint_range(q:Base τ):Set.range (ambientPoint τ hτ q)⊆zeroSet τ hτ:=by
  rintro _ ⟨x,rfl⟩
  rw [ambientPoint_underlying]
  rw [←inclusion_range]
  exact originalPoint_in_candidate τ hτ q

/-- Actual complex-valued Scheme point of the SAME reduced candidate.
The original analytic source has not been silently equipped with an
algebraic structure; this is a pointwise realization, not Chow/GAGA. -/
@[expose] def candidateComplexPoint(q:Base τ):ComplexPoint⟶candidate τ hτ:=
  ReducedSchemePointFactorization318.factor (ambientPoint τ hτ q)
    (zeroSet τ hτ) (ambientPoint_range τ hτ q)
@[reassoc] lemma candidateComplexPoint_inclusion(q:Base τ):
    candidateComplexPoint τ hτ q≫inclusion τ hτ=ambientPoint τ hτ q:=
  ReducedSchemePointFactorization318.factor_inclusion _ _ _
lemma candidateComplexPoint_underlying(q:Base τ)(x:ComplexPoint):
    inclusion τ hτ (candidateComplexPoint τ hτ q x)=originalPoint τ hτ q:=by
  rw [←Scheme.Hom.comp_apply,candidateComplexPoint_inclusion,ambientPoint_underlying]
end PELOriginalCandidateComplexPoints318
