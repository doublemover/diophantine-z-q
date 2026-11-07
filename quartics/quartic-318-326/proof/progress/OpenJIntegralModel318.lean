module
public import AffineIntegralModel318
public import OpenJModel318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace OpenJIntegralModel318
open CategoryTheory AlgebraicGeometry AffineIntegralModel318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable (N:ℕ) (B:Type) [CommRing B]
  [Algebra (OpenJModel318.Base N) B] [Algebra (Polynomial ℤ) B]
  [IsScalarTower (Polynomial ℤ) (OpenJModel318.Base N) B]
  [Module.Finite (OpenJModel318.Base N) B]

/-- Actual integral affine j-model, with its literal denominator. -/
abbrev model := AffineIntegralModel318.model (R:=Polynomial ℤ) (B:=B)
@[expose] def toJLine : model B ⟶ Spec (CommRingCat.of (Polynomial ℤ)) :=
  structureMap (R:=Polynomial ℤ) (B:=B)
@[expose] def originalCover : Spec (CommRingCat.of B) ⟶
    Spec (CommRingCat.of (OpenJModel318.Base N)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) B))
@[expose] def baseOpen : Spec (CommRingCat.of (OpenJModel318.Base N)) ⟶
    Spec (CommRingCat.of (Polynomial ℤ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ) (OpenJModel318.Base N)))

/-- The constructed original cover is finite étale when the genuine input
open algebra is finite étale. -/
theorem original_finite_etale [Algebra.Etale (OpenJModel318.Base N) B] :
    IsFinite (originalCover N B) ∧ Etale (originalCover N B) := by
  constructor
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)

/-- Actual extension of the open j-cover to an integral affine model over Z[j]. -/
theorem model_integral : IsIntegralHom (toJLine B) := structure_integral

/-- The literal denominator-open part of this model is exactly the original
cover, as actual schemes. -/
@[expose] def originalOpenIso : Spec (CommRingCat.of B) ≅
    (modelOpen (B:=B) (OpenJModel318.denominator N)).toScheme :=
  openIso (Rf:=OpenJModel318.Base N) (B:=B) (OpenJModel318.denominator N)

/-- The actual open-cover diagram commutes over the j-line. -/
theorem original_diagram : openMap (R:=Polynomial ℤ) (B:=B) ≫ toJLine B =
    originalCover N B ≫ baseOpen N := by
  rw [toJLine,open_structure]
  unfold originalCover baseOpen
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq (Polynomial ℤ) (OpenJModel318.Base N) B)

end OpenJIntegralModel318
