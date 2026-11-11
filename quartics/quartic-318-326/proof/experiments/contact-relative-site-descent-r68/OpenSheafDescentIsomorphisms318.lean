module
public import OpenSheafDescentMaps318
public section
noncomputable section
namespace OpenSheafDescentIsomorphisms318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenSheafTransition318 OpenSheafDescentMaps318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A B C : X.Modules}

lemma restrictHom_comp {U V : X.Opens} (f : A.over U ⟶ B.over U)
    (g : B.over U ⟶ C.over U) (h : V ≤ U) :
    restrictHom (f ≫ g) h = restrictHom f h ≫ restrictHom g h := by
  simp only [restrictHom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

lemma restrictHom_id {U V : X.Opens} (h : V ≤ U) :
    restrictHom (𝟙 (A.over U)) h = 𝟙 (A.over V) := by
  simp only [restrictHom, Functor.map_id, Category.comp_id, Iso.inv_hom_id]

variable {ι : Type u} {U : ι → X.Opens} {M N P : ι → X.Modules}
  {D : Data U M} {E : Data U N} {F : Data U P}

@[expose] def identity (D : Data U M) : Map D D where
  app i := 𝟙 _
  compatible i j := by rw [restrictHom_id, restrictHom_id, Category.id_comp, Category.comp_id]

@[expose] def compose (f : Map D E) (g : Map E F) : Map D F where
  app i := f.app i ≫ g.app i
  compatible i j := by
    rw [restrictHom_comp, restrictHom_comp, Category.assoc, g.compatible,
      ← Category.assoc, f.compatible, Category.assoc]

lemma scalarMap_identity (D : Data U M) :
    scalarMap (identity D) = OpenModuleDescentMaps318.identity (sectionData D) := by
  apply OpenModuleDescentMaps318.Map.ext
  intro i W hi s
  rfl

lemma scalarMap_compose (f : Map D E) (g : Map E F) :
    scalarMap (compose f g) = OpenModuleDescentMaps318.compose (scalarMap f) (scalarMap g) := by
  apply OpenModuleDescentMaps318.Map.ext
  intro i W hi s
  rfl

lemma gluedMap_identity (D : Data U M) : gluedMap (identity D) = 𝟙 (OpenSheafGluing318.sheaf D) := by
  change OpenModuleDescentMaps318.sheafMap (scalarMap (identity D)) = _
  rw [scalarMap_identity, OpenModuleDescentMaps318.sheafMap_identity]

lemma gluedMap_compose (f : Map D E) (g : Map E F) :
    gluedMap (compose f g) = gluedMap f ≫ gluedMap g := by
  change OpenModuleDescentMaps318.sheafMap (scalarMap (compose f g)) = _
  rw [scalarMap_compose, OpenModuleDescentMaps318.sheafMap_compose]

/-- An isomorphism of the actual original chart data. Compatibility of
its inverse is derived, not supplied as a second descent assumption. -/
structure IsoData (D : Data U M) (E : Data U N) where
  app : ∀ i, (M i).over (U i) ≅ (N i).over (U i)
  compatible : ∀ i j,
    (restrictIso (app i) (show U i ⊓ U j ≤ U i from inf_le_left)).hom ≫ (E.transition i j).hom =
      (D.transition i j).hom ≫ (restrictIso (app j) (show U i ⊓ U j ≤ U j from inf_le_right)).hom

@[expose] def forward (e : IsoData D E) : Map D E where
  app i := (e.app i).hom
  compatible i j := e.compatible i j

@[expose] def backward (e : IsoData D E) : Map E D where
  app i := (e.app i).inv
  compatible i j := by
    let a := restrictIso (e.app i) (show U i ⊓ U j ≤ U i from inf_le_left)
    let b := restrictIso (e.app j) (show U i ⊓ U j ≤ U j from inf_le_right)
    change a.inv ≫ (D.transition i j).hom = (E.transition i j).hom ≫ b.inv
    have h : a.hom ≫ (E.transition i j).hom = (D.transition i j).hom ≫ b.hom := e.compatible i j
    apply (cancel_epi a.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc, h,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Compatible original chart isomorphisms produce an actual global
isomorphism, whose hom satisfies the same recovered chart square. -/
@[expose] def gluedIso (e : IsoData D E) :
    OpenSheafGluing318.sheaf D ≅ OpenSheafGluing318.sheaf E :=
  OpenModuleDescentFullFaithful318.gluedIso (scalarMap (forward e)) (scalarMap (backward e))
    (by
      apply OpenModuleDescentMaps318.Map.ext
      intro i W hi s
      change componentHom ((e.app i).hom ≫ (e.app i).inv) W hi s = s
      rw [Iso.hom_inv_id]
      rfl)
    (by
      apply OpenModuleDescentMaps318.Map.ext
      intro i W hi s
      change componentHom ((e.app i).inv ≫ (e.app i).hom) W hi s = s
      rw [Iso.inv_hom_id]
      rfl)

lemma gluedIso_chart_square (e : IsoData D E) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (gluedIso e).hom ≫
        (OpenSheafGluing318.overIso E i).hom =
      (OpenSheafGluing318.overIso D i).hom ≫ (e.app i).hom :=
  chart_square (forward e) i
end OpenSheafDescentIsomorphisms318
