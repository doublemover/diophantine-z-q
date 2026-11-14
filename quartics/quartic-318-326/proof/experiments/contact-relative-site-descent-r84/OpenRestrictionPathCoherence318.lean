module
public import OpenSheafRestrictionCompatibility318
public section
noncomputable section
namespace OpenRestrictionPathCoherence318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenSheafRestrictionCompatibility318 OpenChartModuleImages318
set_option maxHeartbeats 1800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {U V W : X.Opens}

lemma inclusion_comp (h : W ≤ V) (k : V ≤ U) :
    X.homOfLE h ≫ X.homOfLE k = X.homOfLE (h.trans k) := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

/-- Original restriction collapse on a nested pair of actual chart
inclusions, retaining the actual inclusion composition equality. -/
@[expose] def collapse (h : W ≤ V) (k : V ≤ U) :
    Scheme.Modules.restrictFunctor (X.homOfLE k) ⋙ Scheme.Modules.restrictFunctor (X.homOfLE h) ≅
      Scheme.Modules.restrictFunctor (X.homOfLE (h.trans k)) :=
  (Scheme.Modules.restrictFunctorComp (X.homOfLE h) (X.homOfLE k)).symm ≪≫
    Scheme.Modules.restrictFunctorCongr (inclusion_comp h k)

lemma restrict_map_app {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {A B : Z.Modules} (a : A ⟶ B) (T : Y.Opens) :
    ((Scheme.Modules.restrictFunctor f).map a).app T = a.app (f ''ᵁ T) := rfl

/-- The original named ambient restriction paths compose coherently.
The proof computes the original section restrictions, whose maps are
unique morphisms between these exact opens. -/
lemma path_comp (M : X.Modules) (h : W ≤ V) (k : V ≤ U) :
    path M h ≪≫ (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso (path M k) ≪≫
      (collapse h k).app (M.restrict U.ι) = path M (h.trans k) := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro T
  ext s
  simp only [path, collapse, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrict_map_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, Scheme.Modules.restrict_map]
  simp only [← M.presheaf.map_comp_apply]
  rfl

/-- A specified actual chart comparison is coherent on every nested
subchart. Its restriction naturality is derived from the original collapse. -/
lemma comparison_comp (M : X.Modules) (F : U.toScheme.Modules)
    (e : M.restrict U.ι ≅ F) (h : W ≤ V) (k : V ≤ U) :
    path M h ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso
          (path M k ≪≫ (Scheme.Modules.restrictFunctor (X.homOfLE k)).mapIso e) ≪≫
        (collapse h k).app F =
      path M (h.trans k) ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (h.trans k))).mapIso e := by
  have hn := (collapse h k).hom.naturality e.hom
  simp only [Functor.comp_map] at hn
  have hp := congrArg Iso.hom (path_comp M h k)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hp
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using congrArg
    (fun a => a ≫ (Scheme.Modules.restrictFunctor (X.homOfLE (h.trans k))).map e.hom) hp

lemma subchartRecovery_comp {ι : Type u} (O : ι → X.Opens)
    (F : ∀ i, (O i).toScheme.Modules) (i : ι)
    (h : W ≤ V) (k : V ≤ O i) :
    path (ambient O F i) h ≪≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso (subchartRecovery O F i V k) ≪≫
      (collapse h k).app (F i) = subchartRecovery O F i W (h.trans k) :=
  comparison_comp (ambient O F i) (F i) (chartRecovery O F i) h k
end OpenRestrictionPathCoherence318
