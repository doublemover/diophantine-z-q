module
public import SchemeIsoPushforwardRecovery318
public import AffineModuleBaseChange318
public import OriginalLineAffineBaseChange318
public import PushforwardGlobalSections318

public section
noncomputable section
namespace AffineTensorLinePushforward318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
  {X : Scheme.{u}} (p : X ⟶ Spec A) (j : X ⟶ Spec B)
  (i : Spec (ring R A B) ≅ X)
  (hbase : i.hom ≫ p = Spec.map (leftMap R A B))
  (hchart : i.hom ≫ j = Spec.map (rightMap R A B))
  (L : Line (Spec B)) (M : X.Modules)
  (e : (Scheme.Modules.pullback j).obj L.object ≅ M)

/-- Exact pullback of the original overlap sheaf, identified with the
original chart pullback by its actual tensor chart map. -/
def chartComparison : (Scheme.Modules.pullback i.hom).obj M ≅
    (Scheme.Modules.pullback (Spec.map (rightMap R A B))).obj L.object :=
  (Scheme.Modules.pullback i.hom).mapIso e.symm ≪≫
    (Scheme.Modules.pullbackComp i.hom j).app L.object ≪≫
    (Scheme.Modules.pullbackCongr hchart).app L.object

/-- Original tilde-Gamma affine comparison on the actual tensor chart. -/
def tildeComparison :
    tilde ((ModuleCat.extendScalars (rightMap R A B).hom).obj
      (OriginalLineAffineModel318.sections B L)) ≅ (Scheme.Modules.pullback i.hom).obj M :=
  OriginalLineAffineBaseChange318.sheafIso (rightMap R A B) L ≪≫
    (chartComparison R A B j i hchart L M e).symm

/-- Tensor push-pull, the original affine counit, and the proved scheme
isomorphism over the SAME base identify the scalar extension of the old
polynomial section module with the actual whole-overlap pushforward module.
The A action is preserved throughout, not reconstructed from dimension. -/
def sectionsIso :
    (pullPush R A B).obj (OriginalLineAffineModel318.sections B L) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward p).obj M) :=
  (component R A B (OriginalLineAffineModel318.sections B L)).symm ≪≫
    (ModuleCat.restrictScalars (leftMap R A B).hom).mapIso
      (tilde.isoTop ((ModuleCat.extendScalars (rightMap R A B).hom).obj
        (OriginalLineAffineModel318.sections B L))) ≪≫
    (PushforwardGlobalSections318.globalIso (leftMap R A B)
      (tilde ((ModuleCat.extendScalars (rightMap R A B).hom).obj
        (OriginalLineAffineModel318.sections B L)))).symm ≪≫
    moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.pushforward (Spec.map (leftMap R A B))).mapIso
        (tildeComparison R A B j i hchart L M e)) ≪≫
    moduleSpecΓFunctor.mapIso (SchemeIsoPushforwardRecovery318.overBase i.hom M
      p (Spec.map (leftMap R A B)) hbase)
end AffineTensorLinePushforward318
