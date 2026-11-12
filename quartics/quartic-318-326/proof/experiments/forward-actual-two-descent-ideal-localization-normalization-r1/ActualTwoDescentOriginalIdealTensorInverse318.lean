module
public import ActualTwoDescentOriginalIdealLineObject318
public import FramedLineInverse318
public section
noncomputable section
namespace ActualTwoDescentOriginalIdealTensorInverse318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealLineObject318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The inverse is constructed by inverse ACTUAL transition units of
the produced original frames. It is not postulated from degree zero. -/
def inverseLine (n : K) (hn : n≠0) (i : Fin 3) : LineSheafClass318.Line (originalCubicScheme n) :=
  FramedLineInverse318.inverse (originalLine n hn i)
def rightCancellation (n : K) (hn : n≠0) (i : Fin 3) :
    IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (inverseLine n hn i).object ≅
      SheafOfModules.unit (originalCubicScheme n).ringCatSheaf :=
  FramedLineInverse318.rightIso (originalLine n hn i)
def leftCancellation (n : K) (hn : n≠0) (i : Fin 3) :
    IntrinsicTensorSheaf318.tensor (inverseLine n hn i).object (originalRootIdealSheaf n i) ≅
      SheafOfModules.unit (originalCubicScheme n).ringCatSheaf :=
  FramedLineInverse318.leftIso (originalLine n hn i)

/-- A true tensor-inverse witness for the SAME native global sheaf.
Self-inverseness and the root-function square are NOT inferred. -/
theorem actual_original_ideal_tensor_invertible (n : K) (hn : n≠0) (i : Fin 3) :
    ∃ N : (originalCubicScheme n).Modules,
      Nonempty (IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) N ≅
        SheafOfModules.unit (originalCubicScheme n).ringCatSheaf) ∧
      Nonempty (IntrinsicTensorSheaf318.tensor N (originalRootIdealSheaf n i) ≅
        SheafOfModules.unit (originalCubicScheme n).ringCatSheaf) :=
  ⟨(inverseLine n hn i).object,⟨rightCancellation n hn i⟩,⟨leftCancellation n hn i⟩⟩
end ActualTwoDescentOriginalIdealTensorInverse318
