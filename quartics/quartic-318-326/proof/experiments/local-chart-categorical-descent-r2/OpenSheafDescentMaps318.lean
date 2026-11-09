module
public import OpenModuleDescentFullFaithful318
public import OpenSheafGluing318
public section
noncomputable section
namespace OpenSheafDescentMaps318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenSheafTransition318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A B : X.Modules}

/-- Original over-open restriction of a map, with the same canonical
normalizations used for the original overlap isomorphisms. -/
@[expose] def restrictHom {U V : X.Opens} (f : A.over U ⟶ B.over U) (h : V ≤ U) :
    A.over V ⟶ B.over V :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app A).inv ≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).map f ≫
      ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app B).hom

@[expose] def componentHom {U : X.Opens} (f : A.over U ⟶ B.over U)
    (W : X.Opens) (h : W ≤ U) : Γ(A,W) →ₗ[Γ(X,W)] Γ(B,W) :=
  ((((SheafOfModules.forget (X.ringCatSheaf.over U)) ⋙
    PresheafOfModules.evaluation _ (op (Over.mk (homOfLE h)))).map f)).hom

lemma componentHom_natural {U : X.Opens} (f : A.over U ⟶ B.over U)
    (W V : X.Opens) (hW : W ≤ U) (h : V ≤ W) (s : Γ(A,W)) :
    ModuleLocalGluing318.res B h (componentHom f W hW s) =
      componentHom f V (h.trans hW) (ModuleLocalGluing318.res A h s) := by
  let g : Over.mk (homOfLE (h.trans hW)) ⟶ Over.mk (homOfLE hW) := Over.homMk (homOfLE h)
  exact (PresheafOfModules.naturality_apply f.val g.op s).symm

lemma componentHom_restrict {U V : X.Opens} (f : A.over U ⟶ B.over U)
    (h : V ≤ U) (W : X.Opens) (hW : W ≤ V) (s : Γ(A,W)) :
    componentHom (restrictHom f h) W hW s = componentHom f W (hW.trans h) s := rfl

variable {ι : Type u} {U : ι → X.Opens} {M N P : ι → X.Modules}
/-- Actual sheaf maps on the original chart sites, satisfying exactly the
original pairwise overlap square. No common-subopen family is an extra input. -/
structure Map (D : Data U M) (E : Data U N) where
  app : ∀ i, (M i).over (U i) ⟶ (N i).over (U i)
  compatible : ∀ i j,
    restrictHom (app i) (show U i ⊓ U j ≤ U i from inf_le_left) ≫ (E.transition i j).hom =
      (D.transition i j).hom ≫ restrictHom (app j) (show U i ⊓ U j ≤ U j from inf_le_right)

variable {D : Data U M} {E : Data U N} {F : Data U P}

/-- All-subopen linearity, naturality and compatibility follow from the
original sheaf maps and the original overlap square. -/
@[expose] def scalarMap (f : Map D E) :
    OpenModuleDescentMaps318.Map (sectionData D) (sectionData E) where
  app i W hi := componentHom (f.app i) W hi
  natural i W V hi h s := componentHom_natural (f.app i) W V hi h s
  compatible i j W hi hj s := by
    have h := congrArg (fun k => componentHom k W (le_inf hi hj) s) (f.compatible i j)
    change component (E.transition i j) W (le_inf hi hj)
        (componentHom (restrictHom (f.app i) inf_le_left) W (le_inf hi hj) s) =
      componentHom (restrictHom (f.app j) inf_le_right) W (le_inf hi hj)
        (component (D.transition i j) W (le_inf hi hj) s) at h
    simpa only [componentHom_restrict] using h

abbrev gluedMap (f : Map D E) : OpenSheafGluing318.sheaf D ⟶ OpenSheafGluing318.sheaf E :=
  OpenModuleDescentMaps318.sheafMap (scalarMap f)

/-- The recovered map satisfies the actual categorical chart square,
with the original input map and the displayed object comparison. -/
lemma chart_square (f : Map D E) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (gluedMap f) ≫
        (OpenSheafGluing318.overIso E i).hom =
      (OpenSheafGluing318.overIso D i).hom ≫ f.app i := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext s
  exact OpenModuleDescentMaps318.evaluate_sheafMap (scalarMap f) i W.unop.left (leOfHom W.unop.hom) s

/-- The original categorical chart squares uniquely determine the global map. -/
lemma gluedMap_unique (f : Map D E)
    (g : OpenSheafGluing318.sheaf D ⟶ OpenSheafGluing318.sheaf E)
    (h : ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g ≫
        (OpenSheafGluing318.overIso E i).hom =
      (OpenSheafGluing318.overIso D i).hom ≫ f.app i) : g = gluedMap f := by
  apply OpenModuleDescentFullFaithful318.sheafMap_unique (scalarMap f)
  intro i W hi s
  exact congrArg (fun k => componentHom k W hi s) (h i)

/-- Existence and uniqueness are stated for all actual module-sheaf maps
on X and the unchanged original chart comparisons. -/
theorem effective (f : Map D E) :
    ∃! g : OpenSheafGluing318.sheaf D ⟶ OpenSheafGluing318.sheaf E,
      ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g ≫
          (OpenSheafGluing318.overIso E i).hom =
        (OpenSheafGluing318.overIso D i).hom ≫ f.app i :=
  ⟨gluedMap f, chart_square f, gluedMap_unique f⟩
end OpenSheafDescentMaps318
