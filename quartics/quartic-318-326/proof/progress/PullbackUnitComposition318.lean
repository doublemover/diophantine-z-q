module
public import PullbackScalar318
public section
noncomputable section
namespace PullbackUnitComposition318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ u
lemma homEquiv_mate {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {A : C} {B : D} (k : L₁.obj A ⟶ B) :
    b.homEquiv _ _ (α.app A ≫ k) =
      a.homEquiv _ _ k ≫ (conjugateEquiv a b α).app B := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← unit_conjugateEquiv a b α, Category.assoc,
    ← (conjugateEquiv a b α).naturality k, ← Category.assoc]
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
lemma inverse_composition :
    (Scheme.Modules.pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullback f).map (IdentityCotangent318.pullbackUnitIso g).hom ≫
      (IdentityCotangent318.pullbackUnitIso f).hom =
        (IdentityCotangent318.pullbackUnitIso (f ≫ g)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [homEquiv_mate ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv, PullbackScalar318.adjoint_unit,
    Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.pullback f).map (IdentityCotangent318.pullbackUnitIso g).hom ≫
        (IdentityCotangent318.pullbackUnitIso f).hom)) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app _ = _
  rw [Adjunction.homEquiv_naturality_left, PullbackScalar318.adjoint_unit,
    Adjunction.homEquiv_naturality_right, PullbackScalar318.adjoint_unit]
  exact StructurePushforwardSplit318.unitMap_comp f g
/-- The actual unit comparison for composite scheme pullback agrees with the
successive original unit comparisons. -/
lemma composition :
    (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (IdentityCotangent318.pullbackUnitIso (f ≫ g)).hom =
    (Scheme.Modules.pullback f).map (IdentityCotangent318.pullbackUnitIso g).hom ≫
      (IdentityCotangent318.pullbackUnitIso f).hom := by
  rw [← inverse_composition f g]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
end PullbackUnitComposition318
