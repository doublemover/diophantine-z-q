module
public import FamilyIntrinsicDifferentials318
public section
noncomputable section
namespace StructurePushforwardSplit318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y Z : Scheme.{u}}

/-- Actual structure-sheaf map O_Y -> f_* O_X, as an O_Y-module morphism. -/
@[expose] def unitMap (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- Structure-sheaf maps compose with the genuine pushforward comparison. -/
@[reassoc] theorem unitMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    unitMap g ≫ (Scheme.Modules.pushforward g).map (unitMap f) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app _ = unitMap (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

/-- Structure-sheaf maps respect equality of the underlying scheme morphisms. -/
@[reassoc] theorem unitMap_congr {f g : X ⟶ Y} (h : f = g) :
    unitMap f ≫ (Scheme.Modules.pushforwardCongr h).hom.app _ = unitMap g := by
  subst g
  apply Scheme.Modules.hom_ext
  intro U
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardCongr_hom_app_app]
  simp

/-- Evaluation of regular functions along a genuine section, on every base open. -/
@[expose] def evaluate (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y) :
    (Scheme.Modules.pushforward p).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit Y.ringCatSheaf :=
  (Scheme.Modules.pushforward p).map (unitMap e) ≫
    (Scheme.Modules.pushforwardComp e p).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr he).hom.app _ ≫
    (Scheme.Modules.pushforwardId Y).hom.app _

/-- The structure-sheaf map is always split by evaluation at the section.
Surjectivity of this map is not assumed or asserted. -/
theorem unitMap_evaluate (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y) :
    unitMap p ≫ evaluate p e he = 𝟙 _ := by
  unfold evaluate
  rw [unitMap_comp_assoc, unitMap_congr_assoc]
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

/-- In particular O_Y -> p_*O_X is injective as a sheaf morphism whenever p has
an actual section. This does not prove p_*O_X = O_Y. -/
theorem unitMap_mono (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y) :
    Mono (unitMap p) := by
  exact ⟨fun f g h => by
    have hh := congrArg (fun k => k ≫ evaluate p e he) h
    simpa only [Category.assoc, unitMap_evaluate p e he, Category.comp_id] using hh⟩

variable {R : Type u} [CommRing R]
@[expose] def familyEvaluation (A B : R) :=
  evaluate (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.infinity A B)
    (WeierstrassGluing318.infinity_section A B)

theorem family_structure_split (A B : R) :
    unitMap (WeierstrassGluing318.structureMap A B) ≫ familyEvaluation A B = 𝟙 _ :=
  unitMap_evaluate _ _ _

theorem family_structure_mono (A B : R) :
    Mono (unitMap (WeierstrassGluing318.structureMap A B)) :=
  unitMap_mono _ _ (WeierstrassGluing318.infinity_section A B)
end StructurePushforwardSplit318
