module
public import LocalChartMorphismNormalization318
public import LocalLineOpenDescent318
public section
noncomputable section
namespace LocalChartCategoricalDescent318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenChartModuleImages318 OpenSheafRestrictionCompatibility318 OpenSheafDescentMaps318
set_option maxHeartbeats 2000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A B C D : X.Modules}

/-- Transport the actual ambient scheme square through the original
fully faithful over-open equivalence, keeping both endpoint comparisons. -/
lemma toOver_square (V : X.Opens) (f : A ⟶ B) (g : C ⟶ D)
    (e : A.restrict V.ι ≅ C.restrict V.ι) (e' : B.restrict V.ι ≅ D.restrict V.ι)
    (h : (Scheme.Modules.restrictFunctor V.ι).map f ≫ e'.hom =
      e.hom ≫ (Scheme.Modules.restrictFunctor V.ι).map g) :
    (SheafOfModules.overFunctor X.ringCatSheaf V).map f ≫ (toOverIso V e').hom =
      (toOverIso V e).hom ≫ (SheafOfModules.overFunctor X.ringCatSheaf V).map g := by
  apply (Scheme.Modules.overEquiv V).functor.map_injective
  rw [Functor.map_comp, Functor.map_comp, map_toOver_hom, map_toOver_hom]
  have hf := (Scheme.Modules.overFunctorEquiv V).hom.naturality f
  have hg := (Scheme.Modules.overFunctorEquiv V).hom.naturality g
  change (Scheme.Modules.overEquiv V).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf V).map f) ≫
        ((Scheme.Modules.overFunctorEquiv V).app B).hom =
    ((Scheme.Modules.overFunctorEquiv V).app A).hom ≫ (Scheme.Modules.restrictFunctor V.ι).map f at hf
  change (Scheme.Modules.overEquiv V).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf V).map g) ≫
        ((Scheme.Modules.overFunctorEquiv V).app D).hom =
    ((Scheme.Modules.overFunctorEquiv V).app C).hom ≫ (Scheme.Modules.restrictFunctor V.ι).map g at hg
  apply (cancel_mono ((Scheme.Modules.overFunctorEquiv V).app D).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hg, Iso.inv_hom_id_assoc, ← Category.assoc, hf, Category.assoc, h]

variable {ι : Type u} {U : ι → X.Opens}
  {F G : ∀ i, (U i).toScheme.Modules}
  {d : LocalChartTransition318.Data U F} {e : LocalChartTransition318.Data U G}

abbrev overData (d : LocalChartTransition318.Data U F) :=
  OpenSchemeTransition318.overData (LocalChartTransition318.ambientData d)

/-- The new map consumer takes only original Fi maps and their original
scheme-overlap squares. All direct-image and over-open laws are derived. -/
@[expose] def overMap (f : LocalChartMorphismNormalization318.Map U d e) :
    OpenSheafDescentMaps318.Map (overData d) (overData e) where
  app i := (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map
    (LocalChartMorphismNormalization318.ambientMap U f.app i)
  compatible i j := by
    rw [LocalChartMorphismNormalization318.restrictHom_global,
      LocalChartMorphismNormalization318.restrictHom_global]
    exact toOver_square (U i ⊓ U j)
      (LocalChartMorphismNormalization318.ambientMap U f.app i)
      (LocalChartMorphismNormalization318.ambientMap U f.app j)
      ((LocalChartTransition318.ambientData d).transition i j)
      ((LocalChartTransition318.ambientData e).transition i j)
      (LocalChartMorphismNormalization318.ambient_square f i j)

abbrev object (d : LocalChartTransition318.Data U F) : X.Modules :=
  OpenSheafGluing318.sheaf (overData d)

abbrev comparison (d : LocalChartTransition318.Data U F) (i : ι) :
    (object d).restrict (U i).ι ≅ F i :=
  OpenChartModuleImages318.comparison U F (overData d) i

abbrev gluedMap (f : LocalChartMorphismNormalization318.Map U d e) : object d ⟶ object e :=
  OpenSheafDescentMaps318.gluedMap (overMap f)

/-- The recovered map satisfies the exact original Fi chart square,
including the original restriction/direct-image counit. -/
lemma chart_square (f : LocalChartMorphismNormalization318.Map U d e) (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (gluedMap f) ≫ (comparison e i).hom =
      (comparison d i).hom ≫ f.app i := by
  have h := congrArg ((Scheme.Modules.overEquiv (U i)).functor.map)
    (OpenSheafDescentMaps318.chart_square (overMap f) i)
  simp only [Functor.map_comp] at h
  have hn := (Scheme.Modules.overFunctorEquiv (U i)).inv.naturality (gluedMap f)
  change (Scheme.Modules.restrictFunctor (U i).ι).map (gluedMap f) ≫
      ((Scheme.Modules.overFunctorEquiv (U i)).app (object e)).inv =
    ((Scheme.Modules.overFunctorEquiv (U i)).app (object d)).inv ≫
      (Scheme.Modules.overEquiv (U i)).functor.map
        ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (gluedMap f)) at hn
  have ha := (Scheme.Modules.overFunctorEquiv (U i)).hom.naturality
    (LocalChartMorphismNormalization318.ambientMap U f.app i)
  change (Scheme.Modules.overEquiv (U i)).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).map
        (LocalChartMorphismNormalization318.ambientMap U f.app i)) ≫
      ((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U G i)).hom =
    ((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U F i)).hom ≫
      (Scheme.Modules.restrictFunctor (U i).ι).map
        (LocalChartMorphismNormalization318.ambientMap U f.app i) at ha
  change (Scheme.Modules.restrictFunctor (U i).ι).map (gluedMap f) ≫
      (((Scheme.Modules.overFunctorEquiv (U i)).app (object e)).inv ≫
        (Scheme.Modules.overEquiv (U i)).functor.map (OpenSheafGluing318.overIso (overData e) i).hom ≫
          ((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U G i)).hom ≫ (chartRecovery U G i).hom) =
    (((Scheme.Modules.overFunctorEquiv (U i)).app (object d)).inv ≫
      (Scheme.Modules.overEquiv (U i)).functor.map (OpenSheafGluing318.overIso (overData d) i).hom ≫
        ((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U F i)).hom ≫ (chartRecovery U F i).hom) ≫ f.app i
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U G i)).hom ≫
    (chartRecovery U G i).hom), h]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (chartRecovery U G i).hom, ha, Category.assoc,
    LocalChartMorphismNormalization318.chart_natural]
/-- The original Fi square reflects back to the original over-open square;
no extra compatibility premise is needed for uniqueness. -/
lemma over_square_of_chart (f : LocalChartMorphismNormalization318.Map U d e)
    (g : object d ⟶ object e) (i : ι)
    (h : (Scheme.Modules.restrictFunctor (U i).ι).map g ≫ (comparison e i).hom =
      (comparison d i).hom ≫ f.app i) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g ≫
        (OpenSheafGluing318.overIso (overData e) i).hom =
      (OpenSheafGluing318.overIso (overData d) i).hom ≫ (overMap f).app i := by
  apply (Scheme.Modules.overEquiv (U i)).functor.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  apply (cancel_epi ((Scheme.Modules.overFunctorEquiv (U i)).app (object d)).inv).mp
  apply (cancel_mono (((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U G i)).hom ≫
    (chartRecovery U G i).hom)).mp
  have hn := (Scheme.Modules.overFunctorEquiv (U i)).inv.naturality g
  change (Scheme.Modules.restrictFunctor (U i).ι).map g ≫
      ((Scheme.Modules.overFunctorEquiv (U i)).app (object e)).inv =
    ((Scheme.Modules.overFunctorEquiv (U i)).app (object d)).inv ≫
      (Scheme.Modules.overEquiv (U i)).functor.map
        ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g) at hn
  have ha := (Scheme.Modules.overFunctorEquiv (U i)).hom.naturality
    (LocalChartMorphismNormalization318.ambientMap U f.app i)
  change (Scheme.Modules.overEquiv (U i)).functor.map ((overMap f).app i) ≫
      ((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U G i)).hom =
    ((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U F i)).hom ≫
      (Scheme.Modules.restrictFunctor (U i).ι).map
        (LocalChartMorphismNormalization318.ambientMap U f.app i) at ha
  simp only [Category.assoc]
  rw [← Category.assoc _ _ ((Scheme.Modules.overEquiv (U i)).functor.map
    (OpenSheafGluing318.overIso (overData e) i).hom ≫
      ((Scheme.Modules.overFunctorEquiv (U i)).app (ambient U G i)).hom ≫
        (chartRecovery U G i).hom), ← hn]
  rw [← Category.assoc _ _ (chartRecovery U G i).hom, ha, Category.assoc,
    LocalChartMorphismNormalization318.chart_natural]
  simpa only [comparison, OpenChartModuleImages318.comparison, OpenSheafGluing318.chartIso,
    OpenModuleGluedSheaf318.chartIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc] using h

lemma gluedMap_unique (f : LocalChartMorphismNormalization318.Map U d e)
    (g : object d ⟶ object e)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map g ≫ (comparison e i).hom =
      (comparison d i).hom ≫ f.app i) : g = gluedMap f :=
  OpenSheafDescentMaps318.gluedMap_unique (overMap f) g
    (fun i => over_square_of_chart f g i (h i))

/-- Effective descent of original local module morphisms: existence and
uniqueness use only the actual Fi maps and their actual overlap squares. -/
theorem effective (f : LocalChartMorphismNormalization318.Map U d e) :
    ∃! g : object d ⟶ object e,
      ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map g ≫ (comparison e i).hom =
        (comparison d i).hom ≫ f.app i :=
  ⟨gluedMap f, chart_square f, gluedMap_unique f⟩
end LocalChartCategoricalDescent318
