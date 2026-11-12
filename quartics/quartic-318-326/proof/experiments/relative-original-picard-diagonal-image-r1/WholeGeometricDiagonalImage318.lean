module
public import WholePresheafDiagonalFiber318
public section
noncomputable section
namespace WholeGeometricDiagonalImage318
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w) {B P : C}
  (x y : F.obj (op B)) (p : P ⟶ B) (hp : F.map p.op x=F.map p.op y)
/-- Actual geometric arrows into P give whole equality-fiber points
through the specified projection, with no representability assumption. -/
@[expose] def lift : yoneda.obj P ⟶ WholePresheafDiagonalFiber318.presheaf F x y where
  app T z := ⟨z ≫ p,by
    change F.map (p.op ≫ z.op) x=F.map (p.op ≫ z.op) y
    rw [F.map_comp]
    exact congrArg (F.map z.op) hp⟩
  naturality T U g := by
    funext z
    apply Subtype.ext
    exact Category.assoc _ _ _
lemma projection : lift F x y p hp ≫ WholePresheafDiagonalFiber318.inclusion F x y=yoneda.map p := rfl
/-- The COMPLETE local-image sieve is the actual pulled geometric image,
including every scheme arrow and every factorization through p. -/
lemma image_sieve (T : C) (f : WholePresheafDiagonalFiber318.Object F x y T) :
    Presheaf.imageSieve (lift F x y p hp) f=(MorphismImageSieve318.image p).pullback f.val := by
  ext U g
  change (∃ z : U ⟶ P, (lift F x y p hp).app (op U) z=
    (WholePresheafDiagonalFiber318.presheaf F x y).map g.op f) ↔
      ∃ z : U ⟶ P,z ≫ p=g ≫ f.val
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,congrArg Subtype.val hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,Subtype.ext hz⟩
lemma locallySurjective (J : GrothendieckTopology C)
    (hc : ∀ (T : C) (f : WholePresheafDiagonalFiber318.Object F x y T),
      (MorphismImageSieve318.image p).pullback f.val ∈ J T) :
    Presheaf.IsLocallySurjective J (lift F x y p hp) where
  imageSieve_mem {T} f := by
    rw [image_sieve]
    exact hc T f
end WholeGeometricDiagonalImage318
