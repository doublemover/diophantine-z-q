module
public import OriginalLineBaseChangeUnit318
public import AffineTensorLinePushforward318
public section
noncomputable section
namespace OriginalTensorChartRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
open scoped ChangeOfRings
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
  (L : Line (Spec B))
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Exact tensor-pushout section comparison, before transporting its actual
geometric tensor chart to the displayed overlap scheme. -/
def sectionsIso : (pullPush R A B).obj (OriginalLineAffineModel318.sections B L) ≅
    (ModuleCat.restrictScalars (leftMap R A B).hom).obj
      (OriginalLineAffineModel318.sections (ring R A B)
        (LineSheafPullback318.line (Spec.map (rightMap R A B)) L)) :=
  (component R A B (OriginalLineAffineModel318.sections B L)).symm ≪≫
    (ModuleCat.restrictScalars (leftMap R A B).hom).mapIso
      (OriginalLineAffineBaseChange318.sectionsIso (rightMap R A B) L)

/-- On every original chart section, tensor push-pull sends the original
base scalar-extension unit to the genuine tensor-chart restriction. -/
lemma unit_apply (m : OriginalLineAffineModel318.sections B L) :
    (sectionsIso R A B L).hom
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).unit.app
        ((ModuleCat.restrictScalars (algebraMap R B)).obj
          (OriginalLineAffineModel318.sections B L)) m) =
    (TildePullback318.globalNatIso (rightMap R A B)).hom.app _
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (rightMap R A B))).unit.app L.object) m) := by
  change (OriginalLineAffineBaseChange318.sectionsIso (rightMap R A B) L).hom
    ((component R A B (OriginalLineAffineModel318.sections B L)).inv
      ((1 : A) ⊗ₜ[R, algebraMap R A] m)) = _
  rw [component_inv_tmul]
  change (OriginalLineAffineBaseChange318.sectionsIso (rightMap R A B) L).hom
    ((ModuleCat.extendRestrictScalarsAdj (rightMap R A B).hom).unit.app _ m) = _
  exact OriginalLineBaseChangeUnit318.unit_apply (rightMap R A B) L m

variable {X : Scheme.{u}} (p : X ⟶ Spec A) (j : X ⟶ Spec B)
  (i : Spec (ring R A B) ≅ X)
  (hbase : i.hom ≫ p = Spec.map (leftMap R A B))
  (hchart : i.hom ≫ j = Spec.map (rightMap R A B))
  (M : X.Modules) (e : (Scheme.Modules.pullback j).obj L.object ≅ M)

/-- From genuine sections of the tensor-chart pullback to the SAME original
overlap module, using only the displayed chart comparison and its recovery. -/
def chartRecovery :
    (ModuleCat.restrictScalars (leftMap R A B).hom).obj
      (OriginalLineAffineModel318.sections (ring R A B)
        (LineSheafPullback318.line (Spec.map (rightMap R A B)) L)) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward p).obj M) :=
  (PushforwardGlobalSections318.globalIso (leftMap R A B)
    ((Scheme.Modules.pullback (Spec.map (rightMap R A B))).obj L.object)).symm ≪≫
  moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pushforward (Spec.map (leftMap R A B))).mapIso
      (AffineTensorLinePushforward318.chartComparison R A B j i hchart L M e).symm) ≪≫
  moduleSpecΓFunctor.mapIso (SchemeIsoPushforwardRecovery318.overBase i.hom M
    p (Spec.map (leftMap R A B)) hbase)

/-- The old common-overlap comparison factors through the actual original
chart section comparison. This retains the exact map used to define it. -/
lemma factorization :
    (AffineTensorLinePushforward318.sectionsIso R A B p j i hbase hchart L M e).hom =
      (sectionsIso R A B L).hom ≫ (chartRecovery R A B L p j i hbase hchart M e).hom := by
  have hn := (TildePullback318.globalNatIso (leftMap R A B)).inv.naturality
    (OriginalLineAffineBaseChange318.sheafIso (rightMap R A B) L).hom
  change (ModuleCat.restrictScalars (leftMap R A B).hom).map
      (moduleSpecΓFunctor.map (OriginalLineAffineBaseChange318.sheafIso (rightMap R A B) L).hom) ≫
      (PushforwardGlobalSections318.globalIso (leftMap R A B) _).inv =
    (PushforwardGlobalSections318.globalIso (leftMap R A B) _).inv ≫
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (Spec.map (leftMap R A B))).map
        (OriginalLineAffineBaseChange318.sheafIso (rightMap R A B) L).hom) at hn
  have hn' := congrArg (fun k => k ≫
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (Spec.map (leftMap R A B))).map
      (AffineTensorLinePushforward318.chartComparison R A B j i hchart L M e).inv) ≫
    moduleSpecΓFunctor.map (SchemeIsoPushforwardRecovery318.overBase i.hom M
      p (Spec.map (leftMap R A B)) hbase).hom) hn
  simp only [Category.assoc] at hn'
  simp only [AffineTensorLinePushforward318.sectionsIso, sectionsIso, chartRecovery,
    AffineTensorLinePushforward318.tildeComparison, OriginalLineAffineBaseChange318.sectionsIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc]
  rw [← hn']

/-- The exact old overlap comparison on every scalar-extension unit, now
expressed entirely by original geometric restriction and chart recovery. -/
lemma overlap_unit (m : OriginalLineAffineModel318.sections B L) :
    (AffineTensorLinePushforward318.sectionsIso R A B p j i hbase hchart L M e).hom
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).unit.app
        ((ModuleCat.restrictScalars (algebraMap R B)).obj
          (OriginalLineAffineModel318.sections B L)) m) =
    (chartRecovery R A B L p j i hbase hchart M e).hom
      ((TildePullback318.globalNatIso (rightMap R A B)).hom.app _
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (Spec.map (rightMap R A B))).unit.app L.object) m)) := by
  rw [factorization]
  change (chartRecovery R A B L p j i hbase hchart M e).hom
    ((sectionsIso R A B L).hom _) = _
  rw [unit_apply]
end OriginalTensorChartRestriction318
