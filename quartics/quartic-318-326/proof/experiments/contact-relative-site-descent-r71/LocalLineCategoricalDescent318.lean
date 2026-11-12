module
public import LocalChartCategoricalDescent318
public section
noncomputable section
namespace LocalLineCategoricalDescent318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LocalChartMorphismNormalization318 LocalChartCategoricalDescent318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
  {F G H : ∀ i, (U i).toScheme.Modules}
  {d : LocalChartTransition318.Data U F} {e : LocalChartTransition318.Data U G}
  {k : LocalChartTransition318.Data U H}

@[expose] def identity (d : LocalChartTransition318.Data U F) : Map U d d where
  app i := 𝟙 _
  compatible i j := by rw [Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id]

@[expose] def compose (f : Map U d e) (g : Map U e k) : Map U d k where
  app i := f.app i ≫ g.app i
  compatible i j := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, g.compatible,
      ← Category.assoc, f.compatible, Category.assoc]

lemma gluedMap_identity (d : LocalChartTransition318.Data U F) :
    LocalChartCategoricalDescent318.gluedMap (identity d) = 𝟙 (object d) := by
  symm
  apply LocalChartCategoricalDescent318.gluedMap_unique
  intro i
  simp only [identity, Functor.map_id, Category.id_comp, Category.comp_id]

lemma gluedMap_compose (f : Map U d e) (g : Map U e k) :
    LocalChartCategoricalDescent318.gluedMap (compose f g) =
      LocalChartCategoricalDescent318.gluedMap f ≫ LocalChartCategoricalDescent318.gluedMap g := by
  symm
  apply LocalChartCategoricalDescent318.gluedMap_unique
  intro i
  rw [Functor.map_comp, Category.assoc, LocalChartCategoricalDescent318.chart_square,
    ← Category.assoc, LocalChartCategoricalDescent318.chart_square, Category.assoc]
  rfl

/-- An isomorphism of the original Fi data, retaining its original overlap
square. No ambient sheaf map or inverse compatibility is an input. -/
structure IsoData (d : LocalChartTransition318.Data U F) (e : LocalChartTransition318.Data U G) where
  app : ∀ i, F i ≅ G i
  compatible : ∀ i j,
    (Scheme.Modules.restrictFunctor (X.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left))).map (app i).hom ≫
        (e.transition i j).hom =
      (d.transition i j).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right))).map (app j).hom

@[expose] def forward (a : IsoData d e) : Map U d e where
  app i := (a.app i).hom
  compatible i j := a.compatible i j

@[expose] def backward (a : IsoData d e) : Map U e d where
  app i := (a.app i).inv
  compatible i j := by
    let b := (Scheme.Modules.restrictFunctor
      (X.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left))).mapIso (a.app i)
    let c := (Scheme.Modules.restrictFunctor
      (X.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right))).mapIso (a.app j)
    change b.inv ≫ (d.transition i j).hom = (e.transition i j).hom ≫ c.inv
    have h : b.hom ≫ (e.transition i j).hom = (d.transition i j).hom ≫ c.hom := a.compatible i j
    apply (cancel_epi b.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc, h,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[expose] def gluedIso (a : IsoData d e) : object d ≅ object e where
  hom := LocalChartCategoricalDescent318.gluedMap (forward a)
  inv := LocalChartCategoricalDescent318.gluedMap (backward a)
  hom_inv_id := by
    rw [← gluedMap_compose]
    have h : compose (forward a) (backward a) = identity d := by
      apply Map.ext
      intro i
      exact (a.app i).hom_inv_id
    rw [h, gluedMap_identity]
  inv_hom_id := by
    rw [← gluedMap_compose]
    have h : compose (backward a) (forward a) = identity e := by
      apply Map.ext
      intro i
      exact (a.app i).inv_hom_id
    rw [h, gluedMap_identity]

variable (L K : ∀ i, LineSheafClass318.Line (U i).toScheme)
  (dL : LocalChartTransition318.Data U (fun i => (L i).object))
  (dK : LocalChartTransition318.Data U (fun i => (K i).object))
  (hcover : (⊤ : X.Opens) ≤ iSup U)

/-- Actual local line morphisms descend uniquely to the exact global lines
already produced from the original local line data and covering hypothesis. -/
theorem line_maps_effective (f : Map U dL dK) :
    ∃! g : (LocalLineOpenDescent318.line U L dL hcover).object ⟶
        (LocalLineOpenDescent318.line U K dK hcover).object,
      ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map g ≫
          (LocalLineOpenDescent318.comparison U K dK hcover i).hom =
        (LocalLineOpenDescent318.comparison U L dL hcover i).hom ≫ f.app i :=
  LocalChartCategoricalDescent318.effective f

/-- Original locally isomorphic line descent data yields a global line
isomorphism with its original chart maps, not merely equality of classes. -/
@[expose] def lineIso (a : IsoData dL dK) :
    (LocalLineOpenDescent318.line U L dL hcover).object ≅
      (LocalLineOpenDescent318.line U K dK hcover).object := gluedIso a

lemma lineIso_chart_square (a : IsoData dL dK) (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (lineIso L K dL dK hcover a).hom ≫
        (LocalLineOpenDescent318.comparison U K dK hcover i).hom =
      (LocalLineOpenDescent318.comparison U L dL hcover i).hom ≫ (a.app i).hom :=
  LocalChartCategoricalDescent318.chart_square (forward a) i
end LocalLineCategoricalDescent318
