module
public import OriginalThickenedFrameCocycle318
public import LineFrameIsoCocycle318
public import LinePullbackTransitions318
public import StructureLineFrames318
public import UnitCocycleOne318
import all StructureUnitsSheaf318
public section
noncomputable section
namespace PointedCocycleReductionGauge318
open AlgebraicGeometry CategoryTheory
open PointedLineDeformation318
universe u
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) (L : Deformation i)
    {κ : Type u} (U : κ → X.Opens)
    (frames : ∀ k, SheafOfModules.unit (U k).toScheme.ringCatSheaf ≅ L.line.object.restrict (U k).ι)
@[expose] def pulled (k : κ) : SheafOfModules.unit (i ⁻¹ᵁ U k).toScheme.ringCatSheaf ≅
    ((Scheme.Modules.pullback i).obj L.line.object).restrict (i ⁻¹ᵁ U k).ι :=
  LinePullbackFrames318.frame i L.line.object (U k) (frames k)
/-- The ACTUAL special-fiber trivialization transports the ACTUAL pulled
frames to frames of the original structure line, on full preimage opens. -/
@[expose] def transported (k : κ) : SheafOfModules.unit (i ⁻¹ᵁ U k).toScheme.ringCatSheaf ≅
    Scheme.Modules.restrict (SheafOfModules.unit X₀.ringCatSheaf) (i ⁻¹ᵁ U k).ι :=
  LineFrameIsoCocycle318.transported L.trivialization (fun k => i ⁻¹ᵁ U k) (pulled i L U frames) k
@[expose] def gauge (k : κ) : Γ(X₀,i ⁻¹ᵁ U k)ˣ :=
  LineFrameGauge318.unit (SheafOfModules.unit X₀.ringCatSheaf) (fun k => i ⁻¹ᵁ U k)
    (transported i L U frames) (fun k => StructureLineFrames318.frame X₀ (i ⁻¹ᵁ U k)) k
/-- The original reduced transition is an ACTUAL unit coboundary, including
its exact orientation, on EVERY complete overlap. No claim that independently
chosen pointed frames restrict identically is needed. -/
lemma equation (k l : κ) :
    (1 : (StructureUnitsSheaf318.pushedUnits i).obj.obj (Opposite.op (U k ⊓ U l))) =
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.pushedUnits i).obj U
        (gauge i L U frames) k l *
      (UnitTransitionCocycle318.map (Functor.whiskerRight i.c OpenUnitNorm318.unitsFunctor)
        (LineFrameCocycle318.cocycle L.line.object U frames)).transition k l := by
  have h := InverseImageLineCocycle318.gauge_equation i (SheafOfModules.unit X₀.ringCatSheaf) U
    (transported i L U frames) (fun k => StructureLineFrames318.frame X₀ (i ⁻¹ᵁ U k)) k l
  rw [StructureLineFrames318.inverseImage_transition_one] at h
  change 1 = UnitTransitionCocycle318.coboundary _ U (gauge i L U frames) k l *
    (InverseImageLineCocycle318.cocycle i (SheafOfModules.unit X₀.ringCatSheaf) U
      (LineFrameIsoCocycle318.transported L.trivialization (fun k => i ⁻¹ᵁ U k)
        (pulled i L U frames))).transition k l at h
  rw [LineFrameIsoCocycle318.inverseImage_eq] at h
  change 1 = UnitTransitionCocycle318.coboundary _ U (gauge i L U frames) k l *
    (InverseImageLineCocycle318.cocycle i ((Scheme.Modules.pullback i).obj L.line.object) U
      (fun k => LinePullbackFrames318.frame i L.line.object (U k) (frames k))).transition k l at h
  rw [LinePullbackTransitions318.cocycle] at h
  exact h
/-- The full original pushed-unit cocycle, not a subset of its transitions,
is gauge-equivalent to the actual one cocycle on the special fiber. -/
lemma equivalent : UnitTransitionCocycle318.GaugeEquivalent
    (UnitTransitionCocycle318.map (Functor.whiskerRight i.c OpenUnitNorm318.unitsFunctor)
      (LineFrameCocycle318.cocycle L.line.object U frames))
    (UnitCocycleOne318.one (StructureUnitsSheaf318.pushedUnits i).obj U) :=
  ⟨gauge i L U frames, equation i L U frames⟩
end PointedCocycleReductionGauge318
