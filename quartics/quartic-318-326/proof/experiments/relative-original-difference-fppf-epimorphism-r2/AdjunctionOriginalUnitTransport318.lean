module
public import Mathlib.CategoryTheory.Adjunction.Mates
public section
noncomputable section
namespace AdjunctionOriginalUnitTransport318
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Transport through the genuine mate acts on every transpose, not just on
an identity component. -/
lemma transpose_mate {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (X : C) (Y : D) (f : L₁.obj X ⟶ Y) :
    b.homEquiv X Y (α.app X ≫ f) =
      a.homEquiv X Y f ≫ (conjugateEquiv a b α).app Y := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  rw [← unit_conjugateEquiv a b α X]
  rw [Category.assoc, ← (conjugateEquiv a b α).naturality f, ← Category.assoc]
  rw [← Adjunction.homEquiv_unit]

/-- The original counit, pulled through a second left adjoint and then
transposed, is the image of that second adjunction's actual unit. -/
lemma composite_counit {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {L : C ⥤ D} {R : D ⥤ C} {P : D ⥤ E} {Q : E ⥤ D}
    (a : L ⊣ R) (b : P ⊣ Q) (M : D) :
    (a.comp b).homEquiv (R.obj M) (P.obj M) (P.map (a.counit.app M)) =
      R.map (b.unit.app M) := by
  have hb : b.homEquiv (L.obj (R.obj M)) (P.obj M) (P.map (a.counit.app M)) =
      a.counit.app M ≫ b.unit.app M := by
    rw [Adjunction.homEquiv_unit]
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] using
      (b.unit.naturality (a.counit.app M)).symm
  have ha : a.homEquiv (R.obj M) M (a.counit.app M) = 𝟙 (R.obj M) := by
    rw [Adjunction.homEquiv_unit]
    exact a.right_triangle_components M
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv (R.obj M) (Q.obj (P.obj M))
    (b.homEquiv (L.obj (R.obj M)) (P.obj M) (P.map (a.counit.app M))) = _
  rw [hb,Adjunction.homEquiv_naturality_right]
  change a.homEquiv (R.obj M) M (a.counit.app M) ≫ R.map (b.unit.app M) = _
  rw [ha,Category.id_comp]
end AdjunctionOriginalUnitTransport318
