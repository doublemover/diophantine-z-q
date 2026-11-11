module
public import LineFrameGauge318
public section
noncomputable section
namespace InverseImageLineCocycle318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:X.Modules) {ι:Type v} (V:ι→Y.Opens)
  (frames:∀i,SheafOfModules.unit ((f⁻¹ᵁV i):Scheme).ringCatSheaf≅M.restrict (f⁻¹ᵁV i).ι)
/-- Genuine source transition units as sections of the actual pushed-forward
unit sheaf on the target. Every overlap is the entire inverse image. -/
@[expose] def cocycle:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.pushedUnits f).obj V where
  transition i j:=LineFrameTransitions318.scalar M (fun i=>f⁻¹ᵁV i) frames i j
    (f⁻¹ᵁ(V i⊓V j)) (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
  diagonal i:=LineFrameTransitions318.self M (fun i=>f⁻¹ᵁV i) frames i
    (f⁻¹ᵁ(V i⊓V i)) (f.preimage_mono inf_le_left)
  triple i j k:=by
    change Units.map (X.presheaf.map (homOfLE (f.preimage_mono inf_le_left)).op).hom.toMonoidHom _ *
      Units.map (X.presheaf.map (homOfLE (f.preimage_mono
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right))).op).hom.toMonoidHom _ =
      Units.map (X.presheaf.map (homOfLE (f.preimage_mono
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right))).op).hom.toMonoidHom _
    rw [LineFrameTransitions318.restrict,LineFrameTransitions318.restrict,LineFrameTransitions318.restrict]
    exact LineFrameTransitions318.comp M (fun i=>f⁻¹ᵁV i) frames i j k _ _ _ _
variable (newFrames:∀i,SheafOfModules.unit ((f⁻¹ᵁV i):Scheme).ringCatSheaf≅M.restrict (f⁻¹ᵁV i).ι)
lemma gauge_equation (i j:ι):
    (cocycle f M V newFrames).transition i j=
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.pushedUnits f).obj V
        (LineFrameGauge318.unit M (fun i=>f⁻¹ᵁV i) frames newFrames) i j *
      (cocycle f M V frames).transition i j:=
  LineFrameGauge318.subopen_equation M (fun i=>f⁻¹ᵁV i) frames newFrames i j
    (f⁻¹ᵁ(V i⊓V j)) (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)

lemma gaugeEquivalent:UnitTransitionCocycle318.GaugeEquivalent
    (cocycle f M V frames) (cocycle f M V newFrames):=
  ⟨LineFrameGauge318.unit M (fun i=>f⁻¹ᵁV i) frames newFrames,
    gauge_equation f M V frames newFrames⟩
end InverseImageLineCocycle318
