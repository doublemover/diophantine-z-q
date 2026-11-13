module
public import ContactRelativeFppfSeparated318
public section
noncomputable section
namespace PresheafSingletonSquares318
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)
  {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (a : Y' ⟶ Y) (p : X' ⟶ X)
  (h : g ≫ a = p ≫ f)

include h in
/-- Contravariance for the displayed original square, at an actual section. -/
lemma map_square (y : F.obj (op Y)) :
    F.map g.op (F.map a.op y) = F.map p.op (F.map f.op y) := by
  rw [← Functor.map_comp_apply,← op_comp,h,op_comp,Functor.map_comp_apply]

include h in
/-- A singleton-compatible section stays compatible on any displayed
commuting square. No pullback hypothesis is needed for this direction. -/
lemma compatible (x : F.obj (op X))
    (hx : ∀ {Z : C} (u v : Z ⟶ X), u ≫ f = v ≫ f → F.map u.op x = F.map v.op x) :
    ∀ {Z : C} (u v : Z ⟶ X'), u ≫ g = v ≫ g →
      F.map u.op (F.map p.op x) = F.map v.op (F.map p.op x) := by
  intro Z u v huv
  have hh : (u ≫ p) ≫ f = (v ≫ p) ≫ f := by
    rw [Category.assoc,← h,← Category.assoc,huv,Category.assoc,h,Category.assoc]
  simpa only [op_comp,Functor.map_comp_apply] using hx (u ≫ p) (v ≫ p) hh
end PresheafSingletonSquares318
