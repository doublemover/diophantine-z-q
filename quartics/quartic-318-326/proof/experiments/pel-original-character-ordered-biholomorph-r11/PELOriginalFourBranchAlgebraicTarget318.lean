module
public import ProjectiveLineFourPointAlgebraicNormalization318
public import PELOriginalFourBranchCoordinate318
public section
noncomputable section
namespace PELOriginalFourBranchAlgebraicTarget318
open AlgebraicGeometry CategoryTheory
open PELOriginalMaximalQuotient318 PELOriginalFourBranchCoordinate318
open ProjectiveLineComplexSchemePoints318 ProjectiveLineAlgebraicNormalization318
open ProjectiveLineFourPointAlgebraicNormalization318
open scoped OnePoint

/-- The algebraic automorphism realizes the SAME chosen original analytic
four-branch normalization, with its actual order and actual cross-ratio. -/
@[expose] def realization (i:Fin 4) :=
  fourPoints (sphereBranches i) (sphereBranches_injective i)

@[expose] def originalPoint (q:MaximalBase) : SchemePoints:=spherePoint (originalSphere q)

/-- Postcompose the actual old Spec-C-valued point by the actual algebraic
Scheme isomorphism, rather than merely renaming its analytic coordinate. -/
@[expose] def normalizedPoint (i:Fin 4) (q:MaximalBase) : SchemePoints:=
  pointMap (realization i).schemeIso.hom (realization i).over_base (originalPoint q)

theorem exact_normalized_point (i:Fin 4) (q:MaximalBase) :
    normalizedPoint i q=spherePoint (coordinate i q) := by
  apply Subtype.ext
  exact (realization i).action (originalSphere q)

/-- Exact full morphism-valued images of all four actual branch values. -/
theorem actual_four_images (i:Fin 4) :
    (normalizedPoint i (actualBranches i 0).val).val=(chartPoint 0 0).val ∧
    (normalizedPoint i (actualBranches i 1).val).val=(chartPoint 1 0).val ∧
    (normalizedPoint i (actualBranches i 2).val).val=(chartPoint 1 1).val ∧
    (normalizedPoint i (actualBranches i 3).val).val=(chartPoint 1 (branchParameter i)).val :=
  four_actual_images (sphereBranches i) (sphereBranches_injective i)

/-- This records the WHOLE actual branch subtype at the final Scheme-point
consumer. It does not identify the original double cover with a Legendre
curve, and it makes no arithmetic/rational claim for the parameter. -/
theorem actual_branch_values (i:Fin 4) (q:MaximalBase) :
    q∈PELOriginalCharacterBranches318.CharacterBranchValues i ↔
      normalizedPoint i q=chartPoint 0 0 ∨ normalizedPoint i q=chartPoint 1 0 ∨
      normalizedPoint i q=chartPoint 1 1 ∨ normalizedPoint i q=chartPoint 1 (branchParameter i) := by
  rw [PELOriginalFourBranchCoordinate318.actual_branch_values]
  simp only [exact_normalized_point,←spherePoint_infty,←spherePoint_coe,
    spherePoint_bijective.1.eq_iff]
end PELOriginalFourBranchAlgebraicTarget318
