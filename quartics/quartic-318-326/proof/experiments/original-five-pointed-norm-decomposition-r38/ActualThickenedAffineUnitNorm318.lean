module
public import OriginalOpenDualCoordinates318
public section
noncomputable section
namespace ActualThickenedAffineUnitNorm318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 OriginalThickenedOpenSections318
universe u
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
    (U : Y.Opens) (hU : IsAffineOpen U)
local instance affineTarget : IsAffine U.toScheme := hU
local instance affineSource : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
/-- A genuine multiplicative map on ALL actual units of the original
nonreduced thickened opens, not an assignment only on infinitesimal labels. -/
@[expose] def norm : Γ(thickening R p,π R p ⁻¹ᵁ (f ⁻¹ᵁ U))ˣ →*
    Γ(thickening R q,π R q ⁻¹ᵁ U)ˣ :=
  (OriginalOpenDualCoordinates318.units R q U).comp
    ((OriginalAllOpenDualNorm318.norm f hY hfinite U).comp
      (OriginalOpenDualCoordinates318.inverseUnits R p (f ⁻¹ᵁ U)))
lemma original_preimage (hf : f ≫ q = p) :
    (map R p q f hf) ⁻¹ᵁ (π R q ⁻¹ᵁ U) = π R p ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage]
  change (RelativeLineFunctorPullback318.baseMap p q f hf (structureMap R) ≫
    pullback.fst q (structureMap R)) ⁻¹ᵁ U = _
  rw [RelativeLineFunctorPullback318.baseMap_fst, Scheme.Hom.comp_preimage]
lemma coordinates_value (z : (SquareZeroUnit318.Dual Γ(X,f ⁻¹ᵁ U))ˣ) :
    norm R p q f hY hfinite U hU (OriginalOpenDualCoordinates318.units R p (f ⁻¹ᵁ U) z) =
      OriginalOpenDualCoordinates318.units R q U (OriginalAllOpenDualNorm318.norm f hY hfinite U z) := by
  change OriginalOpenDualCoordinates318.units R q U
    (OriginalAllOpenDualNorm318.norm f hY hfinite U
      (OriginalOpenDualCoordinates318.inverseUnits R p (f ⁻¹ᵁ U)
        (OriginalOpenDualCoordinates318.units R p (f ⁻¹ᵁ U) z))) = _
  rw [OriginalOpenDualCoordinates318.inverse_units]
/-- The actual coefficient units retain the OLD original regular-function norm. -/
lemma coefficient_value (a : Γ(X,f ⁻¹ᵁ U)ˣ) :
    norm R p q f hY hfinite U hU (Units.map ((π R p).app (f ⁻¹ᵁ U)).hom.toMonoidHom a) =
      Units.map ((π R q).app U).hom.toMonoidHom
        (Units.map (OpenDominantNorm318.norm f hY U) a) := by
  rw [← OriginalOpenDualCoordinates318.coefficient_unit, coordinates_value,
    OriginalAllOpenDualNorm318.coefficient_value, OriginalOpenDualCoordinates318.coefficient_unit]
/-- The actual first-order unit square is the OLD all-open trace, before any
passage to cocycles, line classes, or cohomology. -/
lemma infinitesimal_value (a : Γ(X,f ⁻¹ᵁ U)) :
    norm R p q f hY hfinite U hU (OriginalOpenUnitLogarithm318.exp R p (f ⁻¹ᵁ U) a) =
      OriginalOpenUnitLogarithm318.exp R q U (OpenDominantTrace318.trace f hY hfinite U a) := by
  rw [← OriginalOpenDualCoordinates318.infinitesimal_unit, coordinates_value,
    OriginalAllOpenDualNorm318.infinitesimal_value, OriginalOpenDualCoordinates318.infinitesimal_unit]
/-- This same actual map agrees on EVERY unit with the determinant norm of
the actual dual algebra whenever the original entire preimage has a basis. -/
lemma determinant_agreement [Nonempty U] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bs : letI := (f.app U).hom.toAlgebra
      Module.Basis ι Γ(Y,U) Γ(X,f ⁻¹ᵁ U))
    (z : Γ(thickening R p,π R p ⁻¹ᵁ (f ⁻¹ᵁ U))ˣ) :
    letI := (f.app U).hom.toAlgebra
    letI := OriginalDualAlgebraNormTrace318.actualAlgebra Γ(Y,U) Γ(X,f ⁻¹ᵁ U)
    norm R p q f hY hfinite U hU z = OriginalOpenDualCoordinates318.units R q U
      (Units.map (Algebra.norm (DualNumber Γ(Y,U)))
        (OriginalOpenDualCoordinates318.inverseUnits R p (f ⁻¹ᵁ U) z)) := by
  dsimp only [norm, MonoidHom.comp_apply]
  rw [OriginalAllOpenDualNorm318.determinant_agreement f hY hfinite U hU bs]
variable {U} {V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ U)
local instance affineTargetV : IsAffine V.toScheme := hV
local instance affineSourceV : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
/-- Compatibility on every nested pair of actual affine opens, using the
original restrictions on both nonreduced schemes. No overlap is discarded. -/
lemma restrict (z : Γ(thickening R p,π R p ⁻¹ᵁ (f ⁻¹ᵁ U))ˣ) :
    Units.map ((thickening R q).presheaf.map (homOfLE ((π R q).preimage_mono h)).op).hom.toMonoidHom
      (norm R p q f hY hfinite U hU z) =
    norm R p q f hY hfinite V hV
      (Units.map ((thickening R p).presheaf.map
        (homOfLE ((π R p).preimage_mono (f.preimage_mono h))).op).hom.toMonoidHom z) := by
  dsimp only [norm, MonoidHom.comp_apply]
  rw [OriginalOpenDualCoordinates318.units_restrict,
    OriginalAllOpenDualNorm318.restrict, OriginalOpenDualCoordinates318.inverse_restrict]
end ActualThickenedAffineUnitNorm318
