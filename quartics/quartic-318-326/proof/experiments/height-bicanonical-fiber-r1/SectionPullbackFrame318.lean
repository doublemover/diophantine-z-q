module
public import HodgeInvertibilityCriterion318
public section
noncomputable section
namespace SectionPullbackFrame318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules)

/-- Pull back an actual global module section by the original sheaf
pullback/pushforward adjunction unit. -/
@[expose] def pullSection (s : Γ(M, ⊤)) : Γ((Scheme.Modules.pullback p).obj M, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ s

@[expose] def frame (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback p).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullback p).mapIso e ≪≫ IdentityCotangent318.pullbackUnitIso p

/-- Exact normalization: the coefficient of the actual pulled-back
section is its original coefficient pulled back by the actual structure map. -/
theorem frame_section (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) (s : Γ(M, ⊤)) :
    (frame p M e).hom.app ⊤ (pullSection p M s) = p.appTop (e.hom.app ⊤ s) := by
  have h : (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
      (Scheme.Modules.pushforward p).map (frame p M e).hom =
        e.hom ≫ StructurePushforwardSplit318.unitMap p := by
    unfold frame
    rw [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, ← Category.assoc]
    rw [← (Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality e.hom]
    rw [Category.assoc, HodgeInvertibilityCriterion318.adjunction_unit_structure]
  exact congrArg (fun f => f.app ⊤ s) h
end SectionPullbackFrame318
