module
public import OriginalLineBaseChangeUnit318
public section
noncomputable section
namespace OriginalAffineLinePathSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {A B : CommRingCat.{u}} (f : A ⟶ B) (L : Line (Spec A))
  (M : Line (Spec B)) (e : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ M.object)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original scalar-extension comparison followed by the specified actual
geometric path comparison, ending in the unchanged original line sections. -/
def comparison : (ModuleCat.extendScalars f.hom).obj (OriginalLineAffineModel318.sections A L) ≅
    OriginalLineAffineModel318.sections B M :=
  OriginalLineAffineBaseChange318.sectionsIso f L ≪≫ moduleSpecΓFunctor.mapIso e

/-- Restriction defined by the ACTUAL geometric pullback unit and specified
path comparison, independently of the module-extension presentation. -/
@[expose] def restriction (m : OriginalLineAffineModel318.sections A L) : OriginalLineAffineModel318.sections B M :=
  moduleSpecΓFunctor.map e.hom
    ((TildePullback318.globalNatIso f).hom.app _
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app L.object) m))

lemma unit_apply (m : OriginalLineAffineModel318.sections A L) :
    (comparison f L M e).hom ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app _ m) =
      restriction f L M e m := by
  change moduleSpecΓFunctor.map e.hom
    ((OriginalLineAffineBaseChange318.sectionsIso f L).hom _) = _
  rw [OriginalLineBaseChangeUnit318.unit_apply] <;> rfl

lemma restriction_add (m n : OriginalLineAffineModel318.sections A L) :
    restriction f L M e (m+n) = restriction f L M e m + restriction f L M e n := by
  simp only [restriction,map_add]

/-- The actual original restriction is semilinear for the literal original
ring arrow. No abstract change of the section-module action is used. -/
lemma restriction_smul (a : A) (m : OriginalLineAffineModel318.sections A L) :
    restriction f L M e (a • m) = f.hom a • restriction f L M e m := by
  -- Retain the native B-action on the SAME underlying extension carrier;
  -- restriction of scalars otherwise hides it from instance synthesis.
  letI : Module B ((ModuleCat.extendScalars f.hom ⋙ ModuleCat.restrictScalars f.hom).obj
      (OriginalLineAffineModel318.sections A L)) :=
    (inferInstance : Module B ((ModuleCat.extendScalars f.hom).obj
      (OriginalLineAffineModel318.sections A L)))
  rw [← unit_apply,← unit_apply]
  have h := ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app
    (OriginalLineAffineModel318.sections A L)).hom.map_smul a m
  change ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app _ (a • m) :
    (ModuleCat.extendScalars f.hom).obj (OriginalLineAffineModel318.sections A L)) =
      f.hom a • ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app _ m :
        (ModuleCat.extendScalars f.hom).obj (OriginalLineAffineModel318.sections A L)) at h
  rw [h]
  exact (comparison f L M e).hom.hom.map_smul _ _
end OriginalAffineLinePathSections318
