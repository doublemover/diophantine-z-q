module
public import LinePullbackTransitionScalar318
public import InverseImageLineCocycle318
public section
noncomputable section
namespace LinePullbackCocycleReduction318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:Y.Modules) {ι:Type u} (U:ι→Y.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
/-- Full-overlap extraction reduced to exact canonical restrictions. The
coherence hypothesis is explicit; the actual final consumer must prove it. -/
lemma cocycle
    (hc:∀(V W:Y.Opens) (h:W≤V)
      (e:SheafOfModules.unit V.toScheme.ringCatSheaf≅M.restrict V.ι),
      OpenLineFrameRefinement318.frame ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁV)
        (LinePullbackFrames318.frame f M V e) (f⁻¹ᵁW) (f.preimage_mono h)=
      LinePullbackFrames318.frame f M W (OpenLineFrameRefinement318.frame M V e W h)):
    InverseImageLineCocycle318.cocycle f ((Scheme.Modules.pullback f).obj M) U
      (fun i=>LinePullbackFrames318.frame f M (U i) (em i))=
    UnitTransitionCocycle318.map (Functor.whiskerRight f.c OpenUnitNorm318.unitsFunctor)
      (LineFrameCocycle318.cocycle M U em):=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact LinePullbackTransitionScalar318.of_restriction f M (U i) (U j) (U i⊓U j)
    inf_le_left inf_le_right (em i) (em j)
    (hc (U i) (U i⊓U j) inf_le_left (em i))
    (hc (U j) (U i⊓U j) inf_le_right (em j))
end LinePullbackCocycleReduction318
