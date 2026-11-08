module
public import InverseImageLineCocycle318
public import UnitCocycleRefinement318
public section
noncomputable section
namespace InverseImageLineRefinement318
open AlgebraicGeometry CategoryTheory Opposite
open UnitTransitionCocycle318 UnitCocycleRefinement318
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:X.Modules)
    {ι:Type v} {κ:Type w} (U:ι→Y.Opens) (V:κ→Y.Opens)
    (e:∀i,SheafOfModules.unit ((f⁻¹ᵁU i):Scheme).ringCatSheaf≅M.restrict (f⁻¹ᵁU i).ι)
    (d:∀j,SheafOfModules.unit ((f⁻¹ᵁV j):Scheme).ringCatSheaf≅M.restrict (f⁻¹ᵁV j).ι)
@[expose] def leftCocycle:Cocycle (StructureUnitsSheaf318.pushedUnits f).obj (common U V):=
  refine (InverseImageLineCocycle318.cocycle f M U e) (common U V) Prod.fst (fun _=>inf_le_left)
@[expose] def rightCocycle:Cocycle (StructureUnitsSheaf318.pushedUnits f).obj (common U V):=
  refine (InverseImageLineCocycle318.cocycle f M V d) (common U V) Prod.snd (fun _=>inf_le_right)
/-- Exact old-to-new coordinate unit on the whole inverse-image common chart. -/
@[expose] def unit (p:ι×κ):Γ(X,f⁻¹ᵁcommon U V p)ˣ:=
  FrameScalarAlgebra318.scalar
    (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁV p.2) (d p.2) _ (f.preimage_mono inf_le_right))
    (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁU p.1) (e p.1) _ (f.preimage_mono inf_le_left))
lemma unit_restrict (p:ι×κ) (W:Y.Opens) (h:W≤common U V p):
    Units.map (X.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.toMonoidHom (unit f M U V e d p)=
      FrameScalarAlgebra318.scalar
        (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁV p.2) (d p.2) (f⁻¹ᵁW) (f.preimage_mono (h.trans inf_le_right)))
        (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁU p.1) (e p.1) (f⁻¹ᵁW) (f.preimage_mono (h.trans inf_le_left))):=by
  apply Units.ext
  change X.presheaf.map (homOfLE (f.preimage_mono h)).op
    ((OpenLineFrameCoordinates318.frame M (f⁻¹ᵁV p.2) (d p.2) _ _).symm
      (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁU p.1) (e p.1) _ _ 1))=_
  rw [OpenLineFrameCoordinates318.inverse_natural,OpenLineFrameCoordinates318.natural,map_one]
  rfl
lemma left_transition (p q:ι×κ):
    (leftCocycle f M U V e).transition p q=
      FrameScalarAlgebra318.scalar
        (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁU p.1) (e p.1) (f⁻¹ᵁ(common U V p⊓common U V q))
          (f.preimage_mono (inf_le_left.trans inf_le_left)))
        (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁU q.1) (e q.1) (f⁻¹ᵁ(common U V p⊓common U V q))
          (f.preimage_mono (inf_le_right.trans inf_le_left))):=by
  exact LineFrameTransitions318.restrict M (fun i=>f⁻¹ᵁU i) e p.1 q.1
    (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
    (f.preimage_mono (inf_le_inf inf_le_left inf_le_left))
lemma right_transition (p q:ι×κ):
    (rightCocycle f M U V d).transition p q=
      FrameScalarAlgebra318.scalar
        (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁV p.2) (d p.2) (f⁻¹ᵁ(common U V p⊓common U V q))
          (f.preimage_mono (inf_le_left.trans inf_le_right)))
        (OpenLineFrameCoordinates318.frame M (f⁻¹ᵁV q.2) (d q.2) (f⁻¹ᵁ(common U V p⊓common U V q))
          (f.preimage_mono (inf_le_right.trans inf_le_right))):=by
  exact LineFrameTransitions318.restrict M (fun j=>f⁻¹ᵁV j) d p.2 q.2
    (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
    (f.preimage_mono (inf_le_inf inf_le_right inf_le_right))
lemma equation (p q:ι×κ):
    (rightCocycle f M U V d).transition p q=
      coboundary (StructureUnitsSheaf318.pushedUnits f).obj (common U V)
        (unit f M U V e d) p q * (leftCocycle f M U V e).transition p q:=by
  rw [left_transition,right_transition]
  change FrameScalarAlgebra318.scalar _ _ =
    (Units.map (X.presheaf.map (homOfLE (f.preimage_mono inf_le_left)).op).hom.toMonoidHom (unit f M U V e d p)*
      (Units.map (X.presheaf.map (homOfLE (f.preimage_mono inf_le_right)).op).hom.toMonoidHom (unit f M U V e d q))⁻¹)*_
  rw [unit_restrict f M U V e d p _ inf_le_left,unit_restrict f M U V e d q _ inf_le_right]
  exact FrameScalarAlgebra318.gauge _ _ _ _
lemma gaugeEquivalent:GaugeEquivalent (leftCocycle f M U V e) (rightCocycle f M U V d):=
  ⟨unit f M U V e d,equation f M U V e d⟩
end InverseImageLineRefinement318
