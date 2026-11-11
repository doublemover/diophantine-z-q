module
public import LineSheafPullback318
public section
noncomputable section
namespace LineClassPullbackLaws318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y Z : Scheme.{u}}
/-- The original module-sheaf identity pullback comparison, on the actual line. -/
@[expose] def identityIso (L : Line X) :
    (LineSheafPullback318.line (𝟙 X) L).object ≅ L.object :=
  (Scheme.Modules.pullbackId X).app L.object
/-- The original module-sheaf composition comparison, before passing to classes. -/
@[expose] def compositionIso (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line Z) :
    (LineSheafPullback318.line f (LineSheafPullback318.line g L)).object ≅
      (LineSheafPullback318.line (f ≫ g) L).object :=
  (Scheme.Modules.pullbackComp f g).app L.object
lemma identity_hom_inv (L : Line X) :
    (identityIso L).hom ≫ (identityIso L).inv = 𝟙 _ := (identityIso L).hom_inv_id
lemma identity_inv_hom (L : Line X) :
    (identityIso L).inv ≫ (identityIso L).hom = 𝟙 _ := (identityIso L).inv_hom_id
lemma composition_hom_inv (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line Z) :
    (compositionIso f g L).hom ≫ (compositionIso f g L).inv = 𝟙 _ :=
  (compositionIso f g L).hom_inv_id
lemma composition_inv_hom (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line Z) :
    (compositionIso f g L).inv ≫ (compositionIso f g L).hom = 𝟙 _ :=
  (compositionIso f g L).inv_hom_id
lemma pullback_identity (c : Class X) : LineSheafPullback318.pullback (𝟙 X) c = c := by
  induction c using LineSheafClass318.induction with
  | h L => exact classOf_eq (identityIso L)
lemma pullback_composition (f : X ⟶ Y) (g : Y ⟶ Z) (c : Class Z) :
    LineSheafPullback318.pullback (f ≫ g) c =
      LineSheafPullback318.pullback f (LineSheafPullback318.pullback g c) := by
  induction c using LineSheafClass318.induction with
  | h L => exact classOf_eq (compositionIso f g L).symm
lemma pullback_identity_function : LineSheafPullback318.pullback (𝟙 X) = id :=
  funext pullback_identity
lemma pullback_composition_function (f : X ⟶ Y) (g : Y ⟶ Z) :
    LineSheafPullback318.pullback (f ≫ g) =
      LineSheafPullback318.pullback f ∘ LineSheafPullback318.pullback g :=
  funext (pullback_composition f g)
end LineClassPullbackLaws318
