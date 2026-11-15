module
public import ActualThickenedAffineUnitNorm318
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public section
noncomputable section
namespace AffineBasisUnitMaps318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {Y : Scheme.{u}} (F : Y.carrier.Presheaf CommGrpCat.{u})
    (G : TopCat.Sheaf CommGrpCat.{u} Y.carrier)
/-- Actual maps on ALL affine opens, natural for EVERY nested affine pair.
No components on non-affine intersections are assumed. -/
structure Data where
  app : ∀ U : Y.affineOpens, F.obj (op U.1) →* G.obj.obj (op U.1)
  natural : ∀ (U V : Y.affineOpens) (h : V.1 ≤ U.1) (s : F.obj (op U.1)),
    G.obj.map (homOfLE h).op (app U s) = app V (F.map (homOfLE h).op s)
abbrev basis (Y : Scheme.{u}) : Y.affineOpens → Y.Opens := fun U => U.1
lemma basis_range : Set.range (basis Y) = Y.affineOpens := by
  ext U
  constructor
  · rintro ⟨⟨V,hV⟩,rfl⟩
    exact hV
  · intro hU
    exact ⟨⟨U,hU⟩,rfl⟩
lemma isBasis : Opens.IsBasis (Set.range (basis Y)) := by
  simpa only [basis_range] using Y.isBasis_affineOpens
variable {F G} (D : Data F G)
@[expose] def basisMap :
    (inducedFunctor (basis Y)).op ⋙ F ⟶ (inducedFunctor (basis Y)).op ⋙ G.obj where
  app U := CommGrpCat.ofHom (D.app U.unop)
  naturality {U V} h := by
    ext s
    exact (D.natural U.unop V.unop
      (leOfHom ((inducedFunctor (basis Y)).map h.unop)) s).symm
/-- The original sheaf basis-extension equivalence supplies ALL components,
including empty and non-affine intersections, from actual affine data. -/
@[expose] def extend : F ⟶ G.obj :=
  TopCat.Sheaf.restrictHomEquivHom F G (isBasis (Y := Y)) (basisMap D)
lemma extend_affine (U : Y.affineOpens) :
    (extend D).app (op U.1) = CommGrpCat.ofHom (D.app U) :=
  TopCat.Sheaf.extend_hom_app F G (isBasis (Y := Y)) (basisMap D) U
lemma extend_unique (a : F ⟶ G.obj)
    (h : ∀ U : Y.affineOpens, a.app (op U.1) = CommGrpCat.ofHom (D.app U)) : a = extend D := by
  apply TopCat.Sheaf.hom_ext F G (isBasis (Y := Y))
  intro U
  exact (h U).trans (extend_affine D U).symm
end AffineBasisUnitMaps318
