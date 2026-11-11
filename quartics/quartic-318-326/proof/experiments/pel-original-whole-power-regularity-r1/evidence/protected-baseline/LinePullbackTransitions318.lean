module
public import LinePullbackFrameCoherence318
public import LinePullbackCocycleReduction318
public section
noncomputable section
namespace LinePullbackTransitions318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:Y.Modules) {ι:Type u} (U:ι→Y.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
/-- The exact cocycle of the original module-sheaf pullback, on complete
inverse-image intersections, with canonical coherence discharged. -/
lemma cocycle:
    InverseImageLineCocycle318.cocycle f ((Scheme.Modules.pullback f).obj M) U
      (fun i=>LinePullbackFrames318.frame f M (U i) (em i))=
    UnitTransitionCocycle318.map (Functor.whiskerRight f.c OpenUnitNorm318.unitsFunctor)
      (LineFrameCocycle318.cocycle M U em):=
  LinePullbackCocycleReduction318.cocycle f M U em (LinePullbackFrameCoherence318.frame f M)
end LinePullbackTransitions318
