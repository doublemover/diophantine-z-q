module
public import AdjunctionOriginalUnitTransport318
public import TildePullbackMate318
public import OriginalLineAffineBaseChange318
public section
noncomputable section
namespace OriginalLineBaseChangeUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S) (L : Line (Spec R))

/-- The old affine section comparison sends the ORIGINAL scalar-extension
unit to the ORIGINAL geometric pullback unit. Both pushforward and restricted
scalar actions remain displayed. -/
lemma unit_square :
    (ModuleCat.extendRestrictScalarsAdj f.hom).unit.app
        (OriginalLineAffineModel318.sections R L) ≫
      (ModuleCat.restrictScalars f.hom).map
        (OriginalLineAffineBaseChange318.sectionsIso f L).hom =
    moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app L.object) ≫
      (TildePullback318.globalNatIso f).hom.app
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object) := by
  have h := AdjunctionOriginalUnitTransport318.transpose_mate
    ((tilde.adjunction (R:=R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R:=S)))
    (TildePullback318.pullbackIso f).inv
    (OriginalLineAffineModel318.sections R L)
    ((Scheme.Modules.pullback (Spec.map f)).obj L.object)
    ((Scheme.Modules.pullback (Spec.map f)).map L.object.fromTildeΓ)
  rw [TildePullbackMate318.comparison_inverse_mate] at h
  have hc := AdjunctionOriginalUnitTransport318.composite_counit
    (tilde.adjunction (R:=R))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)) L.object
  change ((tilde.adjunction (R:=R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).homEquiv _ _
      ((Scheme.Modules.pullback (Spec.map f)).map L.object.fromTildeΓ) = _ at hc
  rw [hc] at h
  change ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R:=S))).homEquiv _ _
      (OriginalLineAffineBaseChange318.sheafIso f L).hom = _ at h
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply] at h
  have hs : (tilde.adjunction (R:=S)).homEquiv _ _
      (OriginalLineAffineBaseChange318.sheafIso f L).hom =
        (OriginalLineAffineBaseChange318.sectionsIso f L).hom := by
    rw [Adjunction.homEquiv_unit] <;> rfl
  rw [hs, Adjunction.homEquiv_unit] at h
  exact h

/-- On the underlying original sections the unit square gives literal
restriction, rather than merely an abstract isomorphism of modules. -/
lemma unit_apply (m : OriginalLineAffineModel318.sections R L) :
    (OriginalLineAffineBaseChange318.sectionsIso f L).hom
      ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app _ m) =
    (TildePullback318.globalNatIso f).hom.app _
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app L.object) m) := by
  exact congrArg (fun h => h m) (unit_square f L)
end OriginalLineBaseChangeUnit318
