module
public import FourRootActualFiniteRamification318
public import PELOriginalContactSchemePoints318
public section
noncomputable section
namespace PELOriginalAlgebraicFiniteRamification318
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactPoints318
open FourRootActualFractionField318 FourRootAffineTensorPresentation318
open scoped OnePoint
local instance polyAlgebra:Algebra P (A branches):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate branches none)).toAlgebra

/-- The original analytic branch point is the exact complex-valued
point of the same algebraic model, and its actual finite-chart ideal has
ramification index two for the ORIGINAL projective t-coordinate. -/
theorem original_finite_branch (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ)):
    PELOriginalContactSchemePoints318.comparison p=
      FourRootCompletedSchemePoints318.finitePoint branches (finiteCenter p hp j h) ∧
    (FourRootActualResidueInertia318.finitePrime branches (finiteCenter p hp j h)).ramificationIdx P=2:=by
  refine ⟨PELOriginalContactSchemePoints318.finite_value
    (completedMap_finiteBranch p hp j h),?_⟩
  exact FourRootActualFiniteRamification318.ramificationIdx_two branches branches_injective
    j (finiteCenter p hp j h) rfl
end PELOriginalAlgebraicFiniteRamification318
