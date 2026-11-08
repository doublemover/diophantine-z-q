module
public import GenericFiniteCover318
public section
namespace SpecAlgHomComposition318
open AlgebraicGeometry CategoryTheory
universe u
variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]
/-- Contravariant composition stated before concrete coordinate rings are substituted. -/
theorem map_comp (f : T →ₐ[R] U) (g : S →ₐ[R] T) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.toRingHom)=
      Spec.map (CommRingCat.ofHom (f.comp g).toRingHom) := by
  rw [←Spec.map_comp]
  rfl
theorem map_comp_assoc {X : Scheme.{u}} (f : T →ₐ[R] U) (g : S →ₐ[R] T)
    (h : Spec (CommRingCat.of S) ⟶ X) :
    Spec.map (CommRingCat.ofHom (f.comp g).toRingHom) ≫ h=
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ h) := by
  rw [←map_comp f g,Category.assoc]
end SpecAlgHomComposition318
