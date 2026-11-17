module
public import ActualTwoDescentOriginalIdealOpenFrameCover318
public import LineSheafClass318
public section
noncomputable section
namespace ActualTwoDescentOriginalIdealLineObject318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealOpenFrameCover318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A genuine framed line whose object is DEFINITIONALLY the original
global ideal pullback,not a related line chosen from its class. -/
def originalLine (n : K) (hn : n≠0) (i : Fin 3) : LineSheafClass318.Line (originalCubicScheme n) where
  object := originalRootIdealSheaf n i
  Index := ULift.{u} (Option Bool)
  opens := opens n i
  cover := actual_open_cover n hn i
  frame := openFrame n i

/-- Native bundled local freeness,with ONE generator on each actual
covering open. This does not identify any divisor or tensor square. -/
lemma actual_original_ideal_locallyFree (n : K) (hn : n≠0) (i : Fin 3) :
    (originalRootIdealSheaf n i).IsLocallyFree :=
  ModuleFreeOpenFrames318.locallyFree (originalRootIdealSheaf n i) PUnit.{u+1}
    (opens n i) (actual_open_cover n hn i)
    (fun k => coproductUniqueIso (fun _ : PUnit.{u+1} =>
      SheafOfModules.unit (opens n i k).toScheme.ringCatSheaf) ≪≫ openFrame n i k)
end ActualTwoDescentOriginalIdealLineObject318
