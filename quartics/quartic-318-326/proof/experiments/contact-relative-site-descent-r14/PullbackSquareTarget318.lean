module
public import CalibratedPullbackChartComparison318
public section
noncomputable section
namespace PullbackSquareTarget318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

lemma map_hom_inv_assoc {C : Type u} {D : Type v} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {Z : D} (e : A ≅ B) (k : F.obj A ⟶ Z) :
    F.map e.hom ≫ F.map e.inv ≫ k = k := by
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]

lemma map_inv_hom_assoc {C : Type u} {D : Type v} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {Z : D} (e : A ≅ B) (k : F.obj B ⟶ Z) :
    F.map e.inv ≫ F.map e.hom ≫ k = k := by
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

lemma map_inv_hom {C : Type u} {D : Type v} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} (e : A ≅ B) :
    F.map e.inv ≫ F.map e.hom = 𝟙 _ := by
  rw [← Functor.map_comp, Iso.inv_hom_id, F.map_id]

lemma path_target {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c d : X ⟶ Z) (hc : f ≫ g = c) (hd : f ≫ g = d) (h : c = d) :
    (PullbackPathComposition318.iso f g d hd).hom =
      (PullbackPathComposition318.iso f g c hc).hom ≫
        (Scheme.Modules.pullbackCongr h).hom := by
  subst d
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- The original square comparison may be computed through any specified
common composite. Its map does not depend on a newly chosen comparison. -/
lemma cover_common {B B' U U' : Scheme.{u}} (f : U ⟶ B) (g : U' ⟶ B')
    (a : U' ⟶ U) (b : B' ⟶ B) (h : a ≫ f = g ≫ b)
    (c : U' ⟶ B) (ha : a ≫ f = c) (hb : g ≫ b = c) :
    (ActualDescentBaseChangeDiagram318.coverComparison f g a b h).hom =
      (PullbackPathComposition318.iso a f c ha).hom ≫
        (PullbackPathComposition318.iso g b c hb).inv := by
  apply (cancel_mono (PullbackPathComposition318.iso g b c hb).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [path_target g b (g ≫ b) c rfl hb hb,
    path_target a f (g ≫ b) c h ha hb]
  simp only [ActualDescentBaseChangeDiagram318.coverComparison,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

lemma cover_flip {B B' U U' : Scheme.{u}} (f : U ⟶ B) (g : U' ⟶ B')
    (a : U' ⟶ U) (b : B' ⟶ B) (h : a ≫ f = g ≫ b) :
    (ActualDescentBaseChangeDiagram318.coverComparison b a g f h.symm).hom =
      (ActualDescentBaseChangeDiagram318.coverComparison f g a b h).inv := by
  rw [cover_common b a g f h.symm (g ≫ b) rfl h]
  simp only [ActualDescentBaseChangeDiagram318.coverComparison,
    Iso.trans_inv, Iso.symm_inv]
end PullbackSquareTarget318
