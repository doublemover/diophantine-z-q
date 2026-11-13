module
public import ContactGeometricPicardUniversal318
public section
noncomputable section
namespace WholePresheafDiagonalFiber318
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w) {B : C}
  (x y : F.obj (op B))
/-- Actual fiber of equality of the two specified presheaf elements:
its underlying point is a literal arrow to B, not an arbitrary relation label. -/
abbrev Object (T : C) := {f : T ⟶ B // F.map f.op x=F.map f.op y}
@[expose] def map {T U : C} (g : U ⟶ T) (f : Object F x y T) : Object F x y U :=
  ⟨g ≫ f.val,by
    change F.map (f.val.op ≫ g.op) x=F.map (f.val.op ≫ g.op) y
    rw [F.map_comp]
    exact congrArg (F.map g.op) f.property⟩
@[expose] def presheaf : Cᵒᵖ ⥤ Type v where
  obj T := Object F x y T.unop
  map g := map F x y g.unop
  map_id T := by
    funext f
    apply Subtype.ext
    exact Category.id_comp _
  map_comp g h := by
    funext f
    apply Subtype.ext
    exact Category.assoc _ _ _
@[expose] def inclusion : presheaf F x y ⟶ yoneda.obj B where
  app _ f := f.val
  naturality _ _ _ := rfl
lemma inclusion_injective (T : C) : Function.Injective ((inclusion F x y).app (op T)) := by
  intro f g h
  exact Subtype.ext h
end WholePresheafDiagonalFiber318
