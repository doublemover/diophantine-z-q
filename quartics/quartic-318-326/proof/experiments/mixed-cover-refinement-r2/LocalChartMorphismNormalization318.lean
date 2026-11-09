module
public import LocalChartTransition318
public import OpenSheafDescentIsomorphisms318
public section
noncomputable section
namespace LocalChartMorphismNormalization318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenChartModuleImages318 OpenSheafRestrictionCompatibility318
open OpenSheafTransition318 OpenSheafDescentMaps318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A B : X.Modules}

lemma path_natural {U V : X.Opens} (f : A ⟶ B) (h : V ≤ U) :
    (Scheme.Modules.restrictFunctor V.ι).map f ≫ (path B h).hom =
      (path A h).hom ≫ (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((Scheme.Modules.restrictFunctor U.ι).map f) :=
  ((Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X h).symm ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).hom.naturality f)

lemma restrictHom_global (f : A ⟶ B) {U V : X.Opens} (h : V ≤ U) :
    restrictHom ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) h =
      (SheafOfModules.overFunctor X.ringCatSheaf V).map f := by
  have hn := (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).hom.naturality f
  change (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) ≫
        ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app B).hom =
    ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app A).hom ≫
      (SheafOfModules.overFunctor X.ringCatSheaf V).map f at hn
  rw [restrictHom, Category.assoc, hn, Iso.inv_hom_id_assoc]

variable {ι : Type u} (U : ι → X.Opens)
  {F G : ∀ i, (U i).toScheme.Modules}

/-- The ambient morphism is the original direct image of the given Fi map,
not an independently assumed extension to X. -/
@[expose] def ambientMap (f : ∀ i, F i ⟶ G i) (i : ι) : ambient U F i ⟶ ambient U G i :=
  (Scheme.Modules.pushforward (U i).ι).map (f i)

lemma chart_natural (f : ∀ i, F i ⟶ G i) (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (ambientMap U f i) ≫ (chartRecovery U G i).hom =
      (chartRecovery U F i).hom ≫ f i :=
  (Scheme.Modules.restrictFunctorAdjCounitIso (U i).ι).hom.naturality (f i)

/-- Exact compatibility on every original subchart retains both the
original inclusion transport and the original direct-image counit. -/
lemma subchart_natural (f : ∀ i, F i ⟶ G i) (i : ι) (V : X.Opens) (h : V ≤ U i) :
    (Scheme.Modules.restrictFunctor V.ι).map (ambientMap U f i) ≫ (subchartRecovery U G i V h).hom =
      (subchartRecovery U F i V h).hom ≫ (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (f i) := by
  change (Scheme.Modules.restrictFunctor V.ι).map (ambientMap U f i) ≫
      ((path (ambient U G i) h).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (chartRecovery U G i).hom) =
    ((path (ambient U F i) h).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (chartRecovery U F i).hom) ≫ _
  rw [← Category.assoc, path_natural, Category.assoc, ← Functor.map_comp, chart_natural,
    Functor.map_comp, Category.assoc]

/-- Only the original Fi maps and their original scheme-overlap square
are required to map original local descent data. -/
structure Map (D : LocalChartTransition318.Data U F) (E : LocalChartTransition318.Data U G) where
  app : ∀ i, F i ⟶ G i
  compatible : ∀ i j,
    (Scheme.Modules.restrictFunctor (X.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left))).map (app i) ≫
        (E.transition i j).hom =
      (D.transition i j).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right))).map (app j)

variable {U} {D : LocalChartTransition318.Data U F} {E : LocalChartTransition318.Data U G}

@[ext] lemma Map.ext {f g : Map U D E} (h : ∀ i, f.app i = g.app i) : f = g := by
  cases f with | mk f hf =>
    cases g with | mk g hg =>
      have he : f = g := funext h
      subst g
      rfl

/-- The actual original Fi compatibility square transports to the genuine
ambient double intersection using the proved original counit naturality. -/
lemma ambient_square (f : Map U D E) (i j : ι) :
    (Scheme.Modules.restrictFunctor (U i ⊓ U j).ι).map (ambientMap U f.app i) ≫
        ((LocalChartTransition318.ambientData E).transition i j).hom =
      ((LocalChartTransition318.ambientData D).transition i j).hom ≫
        (Scheme.Modules.restrictFunctor (U i ⊓ U j).ι).map (ambientMap U f.app j) := by
  change (Scheme.Modules.restrictFunctor (U i ⊓ U j).ι).map (ambientMap U f.app i) ≫
      ((subchartRecovery U G i (U i ⊓ U j) inf_le_left).hom ≫
        (E.transition i j).hom ≫ (subchartRecovery U G j (U i ⊓ U j) inf_le_right).inv) =
    ((subchartRecovery U F i (U i ⊓ U j) inf_le_left).hom ≫
      (D.transition i j).hom ≫ (subchartRecovery U F j (U i ⊓ U j) inf_le_right).inv) ≫ _
  apply (cancel_mono (subchartRecovery U G j (U i ⊓ U j) inf_le_right).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [subchart_natural U f.app j, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, subchart_natural U f.app i, Category.assoc, f.compatible]
end LocalChartMorphismNormalization318
