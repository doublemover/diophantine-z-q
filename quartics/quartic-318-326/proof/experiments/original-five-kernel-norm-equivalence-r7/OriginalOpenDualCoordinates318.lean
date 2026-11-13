module
public import OriginalAllOpenDualNorm318
public section
noncomputable section
namespace OriginalOpenDualCoordinates318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 OriginalThickenedOpen318 OriginalThickenedOpenSections318
universe u
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R)
    (V : X.Opens) [IsAffine V.toScheme]
local notation "E" => (sectionsIso R p V).commRingCatIsoToRingEquiv
local notation "B" => (baseIso V).commRingCatIsoToRingEquiv
local notation "A" => OriginalAffineDualSectionEquivalence318.equivalence R (localBase R p V)
/-- The full original dual ring, not only its reduced units, is identified
with sections on the ENTIRE thickened affine open by original maps. -/
@[expose] def coordinates : SquareZeroUnit318.Dual Γ(X,V) ≃+*
    Γ(thickening R p,π R p ⁻¹ᵁ V) :=
  ((SquareZeroRingLift318.congr B).trans A).trans E.symm
lemma coefficient (a : Γ(X,V)) : coordinates R p V (TrivSqZeroExt.inl a) = (π R p).app V a := by
  apply E.injective
  calc
    E (coordinates R p V (TrivSqZeroExt.inl a)) = A (TrivSqZeroExt.inl (B a)) := by
      change E (E.symm (A (SquareZeroRingLift318.congr B (TrivSqZeroExt.inl a)))) = _
      rw [E.apply_symm_apply]
      congr 1
      apply TrivSqZeroExt.ext <;> simp [SquareZeroRingLift318.congr, SquareZeroUnit318.map]
    _ = (π R (localBase R p V)).appTop (B a) := by
      change OriginalDualSectionLift318.lift R (localBase R p V) (TrivSqZeroExt.inl (B a)) = _
      simp only [OriginalDualSectionLift318.lift, SquareZeroRingLift318.lift_inl]
    _ = E ((π R p).app V a) :=
      (congrArg (fun f => f a) (coefficient_square R p V)).symm
@[expose] def units : (SquareZeroUnit318.Dual Γ(X,V))ˣ →*
    Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ := Units.map (coordinates R p V).toMonoidHom
@[expose] def inverseUnits : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ →*
    (SquareZeroUnit318.Dual Γ(X,V))ˣ := Units.map (coordinates R p V).symm.toMonoidHom
lemma units_inverse (z : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ) :
    units R p V (inverseUnits R p V z) = z := by
  apply Units.ext
  exact (coordinates R p V).apply_symm_apply z.val
lemma inverse_units (z : (SquareZeroUnit318.Dual Γ(X,V))ˣ) :
    inverseUnits R p V (units R p V z) = z := by
  apply Units.ext
  exact (coordinates R p V).symm_apply_apply z.val
lemma coefficient_unit (a : Γ(X,V)ˣ) :
    units R p V (DualUnitFactorization318.lift Γ(X,V) a) = Units.map ((π R p).app V).hom.toMonoidHom a := by
  apply Units.ext
  exact coefficient R p V a.val
lemma infinitesimal_unit (a : Γ(X,V)) :
    units R p V (SquareZeroUnit318.unit Γ(X,V) a) = OriginalOpenUnitLogarithm318.exp R p V a := by
  apply Units.ext
  change E.symm (A (SquareZeroRingLift318.congr B (SquareZeroUnit318.unit Γ(X,V) a).val)) =
    E.symm (A (SquareZeroUnit318.unit Γ(V.toScheme,⊤) (B a)).val)
  apply congrArg E.symm
  apply congrArg A
  exact congrArg Units.val (SquareZeroUnit318.map_unit Γ(X,V) B.toRingHom a)
variable {V} {W : X.Opens} [IsAffine W.toScheme] (h : W ≤ V)
/-- Actual restriction compatibility on ALL units follows from original
coefficient and epsilon maps, not from a formal change of coordinates. -/
lemma units_restrict (z : (SquareZeroUnit318.Dual Γ(X,V))ˣ) :
    Units.map ((thickening R p).presheaf.map (homOfLE ((π R p).preimage_mono h)).op).hom.toMonoidHom
      (units R p V z) = units R p W
        (Units.map (SquareZeroUnit318.map Γ(X,V) (X.presheaf.map (homOfLE h).op).hom).toMonoidHom z) := by
  have hc (a : Γ(X,V)ˣ) :
      Units.map ((thickening R p).presheaf.map (homOfLE ((π R p).preimage_mono h)).op).hom.toMonoidHom
        (Units.map ((π R p).app V).hom.toMonoidHom a) =
      Units.map ((π R p).app W).hom.toMonoidHom
        (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom a) := by
    apply Units.ext
    exact (congrArg (fun f => f a.val) ((π R p).naturality (homOfLE h).op)).symm
  conv_lhs => rw [← DualUnitFactorization318.factorization Γ(X,V) z]
  rw [map_mul, map_mul, coefficient_unit, infinitesimal_unit, hc,
    OriginalOpenExponentialNaturality318.exp_restrict]
  conv_rhs => rw [← DualUnitFactorization318.factorization Γ(X,V) z]
  rw [map_mul, DualUnitFactorization318.lift_natural, SquareZeroUnit318.map_unit,
    map_mul, coefficient_unit, infinitesimal_unit]
lemma inverse_restrict (z : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ) :
    inverseUnits R p W
      (Units.map ((thickening R p).presheaf.map (homOfLE ((π R p).preimage_mono h)).op).hom.toMonoidHom z) =
    Units.map (SquareZeroUnit318.map Γ(X,V) (X.presheaf.map (homOfLE h).op).hom).toMonoidHom
      (inverseUnits R p V z) := by
  have hh := units_restrict R p h (inverseUnits R p V z)
  rw [units_inverse] at hh
  calc
    _ = inverseUnits R p W (units R p W
        (Units.map (SquareZeroUnit318.map Γ(X,V) (X.presheaf.map (homOfLE h).op).hom).toMonoidHom
          (inverseUnits R p V z))) := congrArg (inverseUnits R p W) hh
    _ = _ := inverse_units R p W _
end OriginalOpenDualCoordinates318
