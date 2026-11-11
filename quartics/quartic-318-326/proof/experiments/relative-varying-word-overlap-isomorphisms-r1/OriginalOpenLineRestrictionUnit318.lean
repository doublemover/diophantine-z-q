module
public import OriginalLineBaseChangeUnit318
public section
noncomputable section
namespace OriginalOpenLineRestrictionUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The canonical restriction/pullback comparison preserves the actual
restriction unit, by the defining original adjunction uniqueness theorem. -/
lemma restriction_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    (Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M
  rw [Adjunction.homEquiv_unit] at h
  exact h

lemma restriction_unit_inverse {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M) =
      (Scheme.Modules.restrictAdjunction f).unit.app M := by
  rw [← restriction_unit f M, Category.assoc, ← Functor.map_comp]
  simp only [Iso.hom_inv_id_app, Functor.map_id, Category.comp_id]

variable {R S : CommRingCat.{u}} (f : R ⟶ S) [IsOpenImmersion (Spec.map f)]
  (L : Line (Spec R))

/-- The original affine section comparison with literal restriction as its
target, retaining the original specified comparison of pullback functors. -/
def sectionsIso : OriginalLineAffineBaseChange318.extendedSections f L ≅
    moduleSpecΓFunctor.obj ((Scheme.Modules.restrictFunctor (Spec.map f)).obj L.object) :=
  OriginalLineAffineBaseChange318.sectionsIso f L ≪≫
    moduleSpecΓFunctor.mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback (Spec.map f)).app L.object).symm)

/-- The scalar-extension unit is precisely the actual original sheaf
restriction map after the displayed section comparison. -/
lemma unit_square :
    (ModuleCat.extendRestrictScalarsAdj f.hom).unit.app
        (OriginalLineAffineModel318.sections R L) ≫
      (ModuleCat.restrictScalars f.hom).map (sectionsIso f L).hom =
    moduleSpecΓFunctor.map
        ((Scheme.Modules.restrictAdjunction (Spec.map f)).unit.app L.object) ≫
      (TildePullback318.globalNatIso f).hom.app
        ((Scheme.Modules.restrictFunctor (Spec.map f)).obj L.object) := by
  simp only [sectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Functor.map_comp, ← Category.assoc, OriginalLineBaseChangeUnit318.unit_square,
    Category.assoc]
  rw [← (TildePullback318.globalNatIso f).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback (Spec.map f)).inv.app L.object)]
  rw [← Category.assoc, ← Functor.map_comp, restriction_unit_inverse]

/-- The target is the original restriction of a section to the open image,
not a replacement tensor coordinate chosen after the fact. -/
lemma unit_apply (m : OriginalLineAffineModel318.sections R L) :
    (sectionsIso f L).hom ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app _ m) =
    (TildePullback318.globalNatIso f).hom.app _
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.restrictAdjunction (Spec.map f)).unit.app L.object) m) :=
  congrArg (fun h => h m) (unit_square f L)
end OriginalOpenLineRestrictionUnit318
