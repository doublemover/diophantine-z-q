module
public import OriginalPullbackSectionComposition318
public import OriginalTensorChartRestriction318
public section
noncomputable section
namespace OriginalTensorChartWholeRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
open OriginalOpenPullbackSections318
set_option maxHeartbeats 700000
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

/-- The actual chart isomorphism carries the original pulled section to
the original tensor-chart section. All units and the original path remain. -/
lemma chart_unit (s : Γ(L.object,⊤)) :
    (AffineTensorLinePushforward318.chartComparison R A B j i hchart L M e).hom.app ⊤
      (sectionPull i.hom M (e.hom.app ⊤ (sectionPull j L.object s))) =
        sectionPull (Spec.map (rightMap R A B)) L.object s := by
  have hn := OriginalPullbackSectionComposition318.naturality i.hom e.inv
    (e.hom.app ⊤ (sectionPull j L.object s))
  have he := ConcreteCategory.congr_hom (congrArg (fun t => t.app ⊤) e.hom_inv_id)
    (sectionPull j L.object s)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ModuleCat.comp_apply, ModuleCat.id_apply] at he
  rw [he] at hn
  change ((PullbackPathComposition318.iso i.hom j (Spec.map (rightMap R A B)) hchart).hom.app
    L.object).app ⊤ (((Scheme.Modules.pullback i.hom).map e.inv).app ⊤
      (sectionPull i.hom M (e.hom.app ⊤ (sectionPull j L.object s)))) = _
  rw [hn]
  exact OriginalPullbackSectionComposition318.path i.hom j _ hchart L.object s

/-- Recovering the original tensor chart gives exactly restriction along
the original overlap edge, followed by its original comparison. -/
lemma recovered_unit (s : Γ(L.object,⊤)) :
    (SchemeIsoPushforwardRecovery318.recovery i.hom M).hom.app ⊤
      ((AffineTensorLinePushforward318.chartComparison R A B j i hchart L M e).inv.app ⊤
        (sectionPull (Spec.map (rightMap R A B)) L.object s)) =
      e.hom.app ⊤ (sectionPull j L.object s) := by
  rw [← chart_unit R A B j i hchart L M e s]
  have he := ConcreteCategory.congr_hom (congrArg (fun t => t.app ⊤)
    (AffineTensorLinePushforward318.chartComparison R A B j i hchart L M e).hom_inv_id)
      (sectionPull i.hom M (e.hom.app ⊤ (sectionPull j L.object s)))
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ModuleCat.comp_apply, ModuleCat.id_apply] at he
  rw [he]
  exact OriginalPullbackSectionComposition318.recovery_apply i.hom M _

/-- The previous tensor-coordinate recovery has this literal underlying
section map. The equality of base maps contributes only the original
identity restriction at the full open; no independent comparison is chosen. -/
lemma chartRecovery_apply
    (t : Γ((Scheme.Modules.pullback (Spec.map (rightMap R A B))).obj L.object,⊤)) :
    (OriginalTensorChartRestriction318.chartRecovery R A B L p j i hbase hchart M e).hom
      ((TildePullback318.globalNatIso (rightMap R A B)).hom.app _ t) =
    (SchemeIsoPushforwardRecovery318.recovery i.hom M).hom.app ⊤
      ((AffineTensorLinePushforward318.chartComparison R A B j i hchart L M e).inv.app ⊤ t) := by
  simp only [OriginalTensorChartRestriction318.chartRecovery,
    SchemeIsoPushforwardRecovery318.overBase,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,Functor.mapIso_inv,Functor.map_comp,
    Scheme.Modules.pushforward_map_app,Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  change (SchemeIsoPushforwardRecovery318.recovery i.hom M).hom.app ⊤
    (((Scheme.Modules.pullback i.hom).obj M).presheaf.map (𝟙 _)
      ((AffineTensorLinePushforward318.chartComparison R A B j i hchart L M e).inv.app ⊤ t)) = _
  rw [Functor.map_id] <;> rfl

/-- Final exact tensor-to-original overlap restriction square. -/
lemma original_restriction (s : Γ(L.object,⊤)) :
    (OriginalTensorChartRestriction318.chartRecovery R A B L p j i hbase hchart M e).hom
      ((TildePullback318.globalNatIso (rightMap R A B)).hom.app _
        (sectionPull (Spec.map (rightMap R A B)) L.object s)) =
      e.hom.app ⊤ (sectionPull j L.object s) := by
  rw [chartRecovery_apply]
  exact recovered_unit R A B j i hchart L M e s
end OriginalTensorChartWholeRestriction318
