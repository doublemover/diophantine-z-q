module
public import FourRootActualInfinityRamification318
public import PELOriginalContactSchemePoints318
public section
noncomputable section
namespace PELOriginalAlgebraicInfinityRamification318
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalContactRootFunctions318 PELOriginalCompletedContactPoints318
open FourRootNormalizedPointCharts318 FourRootInfinityCoordinateRing318
open scoped OnePoint
local instance reciprocalAlgebra:Algebra (Polynomial ℂ) (Ring branches):=
  (Polynomial.aeval (coordinate branches none^2)).toAlgebra

/-- Each ORIGINAL infinity point retains its own sign triple and actual
Scheme-valued center. Algebraic ramification is computed over the exact
reciprocal projective coordinate v=u², including every one of the eight centers. -/
theorem original_infinity_branch (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (h:normalizedMap p=∞):
    PELOriginalContactSchemePoints318.comparison p=
      FourRootCompletedSchemePoints318.infinityPoint branches
        (center branches (infinityCenter p hp h)) ∧
    (FourRootActualResidueInertia318.infinityPrime branches
      (center branches (infinityCenter p hp h))).ramificationIdx (Polynomial ℂ)=2:=by
  refine ⟨PELOriginalContactSchemePoints318.infinity_value
    (completedMap_infinity p hp h),?_⟩
  exact FourRootActualInfinityRamification318.ramificationIdx_two branches branches_injective
    (center branches (infinityCenter p hp h)) rfl
end PELOriginalAlgebraicInfinityRamification318
