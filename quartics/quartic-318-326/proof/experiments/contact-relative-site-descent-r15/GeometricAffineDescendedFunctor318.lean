module
public import GeometricAffineDescendedMorphism318
public section
noncomputable section
namespace GeometricAffineDescendedFunctor318
open AlgebraicGeometry CategoryTheory LineSheafClass318 GeometricAffineDescentData318
open GeometricAffineDescendedMorphism318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : CommRingCat.{u}} [Algebra R S] [Module.FaithfullyFlat R S]

lemma map_id (D : Datum R S) : map (Hom.id D) = 𝟙 (line D).object := by
  symm
  apply map_unique (Hom.id D)
  simp only [Functor.map_id, Category.id_comp, Hom.id, Category.comp_id]

lemma map_comp {D E F : Datum R S} (h : Hom D E) (k : Hom E F) :
    map (h.comp k) = map h ≫ map k := by
  symm
  apply map_unique (h.comp k)
  change _ = (comparison D).hom ≫ (h.sheafHom ≫ k.sheafHom)
  rw [Functor.map_comp, Category.assoc, map_commutes k, ← Category.assoc,
    map_commutes h, Category.assoc]

/-- An actual compatible covering isomorphism descends to an actual
isomorphism of reconstructed base lines, by uniqueness and the original
inverse maps. -/
@[expose] def iso {D E : Datum R S} (h : Hom D E) (k : Hom E D)
    (hk : h.sheafHom ≫ k.sheafHom = 𝟙 D.line.object)
    (kh : k.sheafHom ≫ h.sheafHom = 𝟙 E.line.object) : (line D).object ≅ (line E).object where
  hom := map h
  inv := map k
  hom_inv_id := by
    have he : h.comp k = Hom.id D := Hom.ext hk
    rw [← map_comp, he, map_id]
  inv_hom_id := by
    have he : k.comp h = Hom.id E := Hom.ext kh
    rw [← map_comp, he, map_id]

/-- Actual transition isomorphisms satisfying a covering cocycle descend
with the same exact cocycle. This supplies affine gluing transition maps. -/
lemma map_cocycle {D E F : Datum R S}
    (h : Hom D E) (k : Hom E F) (j : Hom D F)
    (hj : h.sheafHom ≫ k.sheafHom = j.sheafHom) : map h ≫ map k = map j := by
  have he : h.comp k = j := Hom.ext hj
  rw [← map_comp, he]
end GeometricAffineDescendedFunctor318
