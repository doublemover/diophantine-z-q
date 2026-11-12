module
public import ComplexSphereUnorderedInvariant318
public import PELOriginalOrderedLegendreInvariants318
public section
noncomputable section
namespace PELOriginalEnumerationInvariant318
open scoped OnePoint
open ComplexProjectiveCrossRatio318 ComplexSphereActualCrossRatio318
open ComplexSphereUnorderedInvariant318 ComplexLegendreCoordinates318
open NormalizedLegendreProjectiveModel318

/-- The fixed manuscript quadruple is the original arbitrary quadruple
under its EXACT known permutation and the actual global normalization. -/
lemma actual_points_reordered (i : Fin 4) :
    PELOriginalOrderedCharacterCoordinate318.points i=
      fun j=>ComplexSphereFourPointNormalization318.normalization
        PELOriginalManuscriptNormalization318.points
        PELOriginalManuscriptNormalization318.points_injective
        (PELOriginalFourBranchCoordinate318.sphereBranches i
          (PELOriginalOrderedCharacterCoordinate318.oldOrder i j)) := by
  funext j
  change ComplexSphereFourPointNormalization318.normalization _ _
    (PELOriginalFourBranchCoordinate318.originalSphere
      (PELOriginalOrderedCharacterCoordinate318.branches i j).val)=
    ComplexSphereFourPointNormalization318.normalization _ _
    (PELOriginalFourBranchCoordinate318.originalSphere
      (PELOriginalFourBranchCoordinate318.actualBranches i
        (PELOriginalOrderedCharacterCoordinate318.oldOrder i j)).val)
  rw [PELOriginalOrderedCharacterCoordinate318.oldOrder_exact]

/-- No numerical or branch-set shortcut: both the arbitrary enumeration
and the global manuscript change are explicitly cancelled on the original
points before the invariant is reused. -/
theorem ordered_j_eq_original (i : Fin 4) :
    legendreJ (PELOriginalOrderedCharacterCoordinate318.parameter i)=
      legendreJ (PELOriginalFourBranchCoordinate318.branchParameter i) := by
  unfold PELOriginalOrderedCharacterCoordinate318.parameter
    PELOriginalFourBranchCoordinate318.branchParameter
  rw [parameter_eq_crossRatio,parameter_eq_crossRatio,actual_points_reordered,
    crossRatio_normalization]
  exact crossRatio_j_permutation _
    (PELOriginalFourBranchCoordinate318.sphereBranches_injective i)
    (PELOriginalOrderedCharacterCoordinate318.oldOrder i)

@[expose] def originalInvariant (i : Fin 4) : ℂ := by
  let t:=PELOriginalFourBranchCoordinate318.branchParameter i
  letI:=curve_elliptic t
    (PELOriginalFourBranchCoordinate318.branchParameter_nonexceptional i).1
    (PELOriginalFourBranchCoordinate318.branchParameter_nonexceptional i).2
  exact (curve t).j
lemma originalInvariant_formula (i : Fin 4) :
    originalInvariant i=legendreJ (PELOriginalFourBranchCoordinate318.branchParameter i) := by
  have h:=curve_j (PELOriginalFourBranchCoordinate318.branchParameter i)
    (PELOriginalFourBranchCoordinate318.branchParameter_nonexceptional i).1
    (PELOriginalFourBranchCoordinate318.branchParameter_nonexceptional i).2
  change originalInvariant i=256*((PELOriginalFourBranchCoordinate318.branchParameter i)^2-
    PELOriginalFourBranchCoordinate318.branchParameter i+1)^3/
    ((PELOriginalFourBranchCoordinate318.branchParameter i)^2*
      (PELOriginalFourBranchCoordinate318.branchParameter i-1)^2) at h
  rw [h]
  unfold legendreJ
  congr 1
  · congr 1
    ring
  · ring

/-- SAME native Weierstrass invariant of the earlier candidate Legendre
curve. This does not assert that either candidate already represents the
original analytic double cover. -/
theorem ordered_invariant_eq_original (i : Fin 4) :
    PELOriginalOrderedLegendreInvariants318.invariant i=originalInvariant i := by
  rw [PELOriginalOrderedLegendreInvariants318.invariant_formula,
    originalInvariant_formula,ordered_j_eq_original]
end PELOriginalEnumerationInvariant318
