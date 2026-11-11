module
public import BinaryFramedPowerComparison318
public import FramedLineCocycleIso318
public section
noncomputable section
namespace OriginalBinaryFrameComparison318
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U V : X.Opens)
  (em : ∀ i : ULift.{u} Bool, SheafOfModules.unit
    (OpenClutchedLocallyFree318.cover U V i).toScheme.ringCatSheaf ≅
      M.restrict (OpenClutchedLocallyFree318.cover U V i).ι)
  (en : ∀ i : ULift.{u} Bool, SheafOfModules.unit
    (OpenClutchedLocallyFree318.cover U V i).toScheme.ringCatSheaf ≅
      N.restrict (OpenClutchedLocallyFree318.cover U V i).ι)
  (h : (LineFrameCocycle318.cocycle M (OpenClutchedLocallyFree318.cover U V) em).transition
      ⟨false⟩ ⟨true⟩ =
    (LineFrameCocycle318.cocycle N (OpenClutchedLocallyFree318.cover U V) en).transition
      ⟨false⟩ ⟨true⟩)
include h in
lemma cocycle : LineFrameCocycle318.cocycle M (OpenClutchedLocallyFree318.cover U V) em =
    LineFrameCocycle318.cocycle N (OpenClutchedLocallyFree318.cover U V) en := by
  have hp := BinaryFramedPowerComparison318.cocycle_power N M U V en em 1
    (by simpa only [pow_one] using h)
  exact hp.trans (by
    apply UnitTransitionCocycle318.Cocycle.ext
    intro i j
    exact pow_one _)

/-- Actual original sheaf comparison retaining both complete chart frames. -/
@[expose] def iso (hc : U ⊔ V = ⊤) : M ≅ N :=
  FramedLineCocycleIso318.iso M N (OpenClutchedLocallyFree318.cover U V) em en
    (OpenClutchedLocallyFree318.cover_top U V hc) (cocycle M N U V em en h)

lemma coordinate (hc : U ⊔ V = ⊤) (i : ULift.{u} Bool) :
    (iso M N U V em en h hc).hom ≫
      LineFrameAdjunction318.coordinate N (OpenClutchedLocallyFree318.cover U V i) (en i) =
        LineFrameAdjunction318.coordinate M (OpenClutchedLocallyFree318.cover U V i) (em i) :=
  FramedLineCocycleIso318.coordinate M N _ em en _ _ i
end OriginalBinaryFrameComparison318
