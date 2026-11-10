module
public import OriginalLineNamedComparison318
public section
noncomputable section
namespace AffineSectionConjugation318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineAffineBaseChange318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂ u₁ u₂

/-- Conjugation by fixed comparison isomorphisms preserves composition. -/
lemma conjugate_comp {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) {A B C' : C} {A' B' C'' : D}
    (a : A' ≅ F.obj A) (b : B' ≅ F.obj B) (c : C'' ≅ F.obj C')
    (f : A ⟶ B) (g : B ⟶ C') :
    (a.hom ≫ F.map f ≫ b.inv) ≫ (b.hom ≫ F.map g ≫ c.inv) =
      a.hom ≫ F.map (f ≫ g) ≫ c.inv := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- Canonical endpoint squares transport a normalized geometric edge
without changing either endpoint object or the underlying morphism. -/
lemma normalized {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) {A B A₁ B₁ : C} {A' B' A₁' B₁' : D}
    (s : A' ≅ F.obj A) (t : B' ≅ F.obj B)
    (v : A₁' ≅ F.obj A₁) (w : B₁' ≅ F.obj B₁)
    (d : A ≅ A₁) (e : B ≅ B₁) (c : A' ≅ A₁') (k : B' ≅ B₁')
    (hd : c.hom ≫ v.hom = s.hom ≫ F.map d.hom)
    (he : k.hom ≫ w.hom = t.hom ≫ F.map e.hom) (h : A ⟶ B) :
    v.hom ≫ F.map (d.inv ≫ h ≫ e.hom) ≫ w.inv =
      c.inv ≫ (s.hom ≫ F.map h ≫ t.inv) ≫ k.hom := by
  have hv : v = c.symm ≪≫ s ≪≫ F.mapIso d := by
    apply Iso.ext
    apply (cancel_epi c.hom).mp
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.hom_inv_id_assoc] using hd
  have hw : w = k.symm ≪≫ t ≪≫ F.mapIso e := by
    apply Iso.ext
    apply (cancel_epi k.hom).mp
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.hom_inv_id_assoc] using he
  rw [hv, hw]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc,
    Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]

variable {R S T : CommRingCat.{u}} (L : Line (Spec R))

@[expose] def morphism (f g : R ⟶ S)
    (h : (LineSheafPullback318.line (Spec.map f) L).object ⟶
      (LineSheafPullback318.line (Spec.map g) L).object) :
    (ModuleCat.extendScalars f.hom).obj (OriginalLineAffineModel318.sections R L) ⟶
      (ModuleCat.extendScalars g.hom).obj (OriginalLineAffineModel318.sections R L) :=
  (sectionsIso f L).hom ≫ moduleSpecΓFunctor.map h ≫ (sectionsIso g L).inv

lemma morphism_comp (f g k : R ⟶ S)
    (h : (LineSheafPullback318.line (Spec.map f) L).object ⟶
      (LineSheafPullback318.line (Spec.map g) L).object)
    (j : (LineSheafPullback318.line (Spec.map g) L).object ⟶
      (LineSheafPullback318.line (Spec.map k) L).object) :
    morphism L f g h ≫ morphism L g k j = morphism L f k (h ≫ j) :=
  conjugate_comp _ _ _ _ _ _

/-- The two endpoint comparisons for pulling back an arbitrary original
sheaf morphism intertwine its actual global sections with scalar extension. -/
lemma pulled_morphism (f g : R ⟶ S) (m : S ⟶ T)
    (h : (LineSheafPullback318.line (Spec.map f) L).object ⟶
      (LineSheafPullback318.line (Spec.map g) L).object) :
    let a := (ModuleCat.extendScalars m.hom).mapIso (sectionsIso f L) ≪≫
      sectionsIso m (LineSheafPullback318.line (Spec.map f) L)
    let b := (ModuleCat.extendScalars m.hom).mapIso (sectionsIso g L) ≪≫
      sectionsIso m (LineSheafPullback318.line (Spec.map g) L)
    a.hom ≫ moduleSpecΓFunctor.map ((Scheme.Modules.pullback (Spec.map m)).map h) ≫ b.inv =
      (ModuleCat.extendScalars m.hom).map (morphism L f g h) := by
  dsimp only
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc]
  rw [← OriginalLineComparisonComposition318.sectionsIso_naturality_assoc m
    (LineSheafPullback318.line (Spec.map f) L) (LineSheafPullback318.line (Spec.map g) L) h]
  simp only [morphism, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
end AffineSectionConjugation318
