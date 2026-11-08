module
public import UnitTransitionCocycle318
public import FifthSheafNorm318
public section
noncomputable section
namespace FifthNormCocycle318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open FifthCompletedGlobal318
open UnitTransitionCocycle318
universe v
set_option maxHeartbeats 250000
/-- Transition units on the inverse images of the specified target opens. -/
abbrev SourceCocycle {ι : Type v} (U : ι → Target.Opens) :=
  Cocycle (StructureUnitsSheaf318.pushedUnits map).obj U
/-- Transition units on the specified actual target opens. -/
abbrev TargetCocycle {ι : Type v} (U : ι → Target.Opens) :=
  Cocycle (StructureUnitsSheaf318.units Target).obj U
/-- Actual fifth-map unit norm on every complete transition overlap. This
requires source trivializations on inverse images of the given target opens. -/
@[expose] def transfer {ι : Type v} {U : ι → Target.Opens}
    (c : SourceCocycle U) : TargetCocycle U :=
  UnitTransitionCocycle318.map FifthSheafNorm318.norm.hom c
@[expose] def pullback {ι : Type v} {U : ι → Target.Opens}
    (c : TargetCocycle U) : SourceCocycle U :=
  UnitTransitionCocycle318.map FifthSheafNorm318.pullback.hom c
lemma transition {ι : Type v} {U : ι → Target.Opens} (c : SourceCocycle U) (i j : ι) :
    (transfer c).transition i j =
      FifthOpenNorm318.unitNorm.app (op (U i ⊓ U j)) (c.transition i j) := rfl
/-- Explicit target coboundary induced by the actual source change of frame. -/
lemma coboundary {ι : Type v} (U : ι → Target.Opens)
    (a : ∀ i, (StructureUnitsSheaf318.pushedUnits map).obj.obj (op (U i))) (i j : ι) :
    FifthSheafNorm318.norm.hom.app (op (U i ⊓ U j))
      (UnitTransitionCocycle318.coboundary
        (StructureUnitsSheaf318.pushedUnits map).obj U a i j) =
    UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units Target).obj U
      (fun k => FifthSheafNorm318.norm.hom.app (op (U k)) (a k)) i j :=
  map_coboundary FifthSheafNorm318.norm.hom U a i j
lemma gaugeEquivalent {ι : Type v} {U : ι → Target.Opens}
    {c d : SourceCocycle U} (h : GaugeEquivalent c d) :
    GaugeEquivalent (transfer c) (transfer d) :=
  map_gaugeEquivalent FifthSheafNorm318.norm.hom h
/-- Pullback followed by norm is the literal eighth power of each original
transition unit, not an asserted global Picard identification. -/
lemma pullback_transition {ι : Type v} {U : ι → Target.Opens}
    (c : TargetCocycle U) (i j : ι) :
    (transfer (pullback c)).transition i j = (c.transition i j) ^ 8 := by
  exact FifthOpenNorm318.unit_pullback (U i ⊓ U j) (c.transition i j)
lemma pullback_transfer {ι : Type v} {U : ι → Target.Opens}
    (c : TargetCocycle U) :
    transfer (pullback c) = UnitTransitionCocycle318.map FifthSheafNorm318.eighthPower.hom c := by
  apply Cocycle.ext
  intro i j
  exact pullback_transition c i j
end FifthNormCocycle318
