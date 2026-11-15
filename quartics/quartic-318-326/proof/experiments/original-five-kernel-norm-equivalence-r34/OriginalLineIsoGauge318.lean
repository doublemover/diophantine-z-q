module
public import OriginalHOnePointedSurjection318
public section
noncomputable section
namespace OriginalLineIsoGauge318
open AlgebraicGeometry CategoryTheory
universe u
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {κ : Type u} (U : κ → X.Opens)
    (c d : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
/-- Any isomorphism of the ORIGINAL coefficient-module sheaves supplies the
actual original frame gauge on the unchanged whole cover. -/
lemma equivalent (e : CocycleModule318.object U c ≅ CocycleModule318.object U d) :
    UnitTransitionCocycle318.GaugeEquivalent c d := by
  have h := LineFrameGauge318.equivalent (CocycleModule318.object U d) U
    (LineFrameIsoCocycle318.transported e U (CocycleCanonicalTransitions318.frames U c))
    (CocycleCanonicalTransitions318.frames U d)
  rw [LineFrameIsoCocycle318.cocycle_eq, CocycleCanonicalTransitions318.cocycle_eq,
    CocycleCanonicalTransitions318.cocycle_eq] at h
  exact h
end OriginalLineIsoGauge318
