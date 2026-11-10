module
public import Mathlib.AlgebraicGeometry.Normalization
public section
noncomputable section
namespace NormalizationSourceIso318
open AlgebraicGeometry CategoryTheory
universe u
variable {X X' B : Scheme.{u}} (f : X ⟶ B) (g : X' ⟶ B)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]

/-- Functoriality on the SAME relative normalization, constructed by its
actual universal property over the original base. -/
@[expose] def map (a : X ⟶ X') (h : a ≫ g = f) : f.normalization ⟶ g.normalization :=
  f.normalizationDesc (a ≫ g.toNormalization) g.fromNormalization (by
    rw [Category.assoc, g.toNormalization_fromNormalization, h])

@[reassoc (attr := simp)] theorem map_source (a : X ⟶ X') (h : a ≫ g = f) :
    f.toNormalization ≫ map f g a h = a ≫ g.toNormalization :=
  f.toNormalization_normalizationDesc _ _ _

@[reassoc (attr := simp)] theorem map_base (a : X ⟶ X') (h : a ≫ g = f) :
    map f g a h ≫ g.fromNormalization = f.fromNormalization :=
  f.normalizationDesc_comp _ _ _

/-- A given source isomorphism induces an isomorphism of actual globally
glued relative normalizations. Its source square fixes the induced map. -/
@[expose] def iso (e : X ≅ X') (h : e.hom ≫ g = f) : f.normalization ≅ g.normalization where
  hom := map f g e.hom h
  inv := map g f e.inv (by rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp])
  hom_inv_id := by
    apply f.normalization.hom_ext _ _ f.fromNormalization
    · simp only [map_source_assoc, map_source, e.hom_inv_id_assoc, Category.comp_id]
    · simp only [Category.assoc, map_base]
    · simp
  inv_hom_id := by
    apply g.normalization.hom_ext _ _ g.fromNormalization
    · simp only [map_source_assoc, map_source, e.inv_hom_id_assoc, Category.comp_id]
    · simp only [Category.assoc, map_base]
    · simp

@[reassoc] theorem iso_source (e : X ≅ X') (h : e.hom ≫ g = f) :
    f.toNormalization ≫ (iso f g e h).hom = e.hom ≫ g.toNormalization :=
  map_source f g e.hom h

@[reassoc] theorem iso_base (e : X ≅ X') (h : e.hom ≫ g = f) :
    (iso f g e h).hom ≫ g.fromNormalization = f.fromNormalization :=
  map_base f g e.hom h
end NormalizationSourceIso318
