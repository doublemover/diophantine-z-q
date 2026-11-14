module
public import FourRootDerivativeZeroSections318
public import FiniteEtaleFieldPoints318
public import CartesianSectionPoints318
public section
noncomputable section
namespace FourRootZeroGlobalSectionPoints318
open AlgebraicGeometry CategoryTheory
open FourRootGluedDerivativeIdeal318 FourRootDerivativeZeroSections318
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
local instance affine : IsAffine (zeroScheme b) := FourRootDerivativeZeroFinite318.affine b hb
/-- The canonical affine identification preserves the ACTUAL structural
C action used in H0, by the genuine naturality of global sections. -/
lemma iso_over_base : (zeroScheme b).isoSpec.hom ≫ Spec.algebraMap ℂ (H0 b) =
    FourRootDerivativeZeroFinite318.structure b := by
  change (zeroScheme b).isoSpec.hom ≫ Spec.map
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      (FourRootDerivativeZeroFinite318.structure b).appTop) = _
  rw [Spec.map_comp,←Category.assoc,Scheme.isoSpec_hom_naturality,
    Category.assoc,←Scheme.isoSpec_Spec_inv,Iso.hom_inv_id,Category.comp_id]
abbrev Points := {p : Spec (CommRingCat.of ℂ) ⟶ zeroScheme b //
  p ≫ FourRootDerivativeZeroFinite318.structure b = 𝟙 _}
/-- True base-preserving scheme points correspond to H0 algebra points,
not via a chosen labeling of a finite set. -/
@[expose] def pointEquiv : Points b ≃ FiniteEtaleFieldPoints318.Points ℂ (H0 b) :=
  CartesianSectionPoints318.isoEquiv (zeroScheme b).isoSpec
    (FourRootDerivativeZeroFinite318.structure b) (Spec.algebraMap ℂ (H0 b))
    (iso_over_base b hb)
/-- The actual dimension is the cardinality of the actual entire point
set. The later original ramification identification must supply40. -/
theorem card_eq_finrank : Nat.card (Points b) = Module.finrank ℂ (H0 b) := by
  letI := FourRootDerivativeZeroSections318.finite b hb
  letI := FourRootDerivativeZeroSections318.etale b hb
  exact (Nat.card_congr (pointEquiv b hb)).trans
    (FiniteEtaleFieldPoints318.card_points ℂ (H0 b))
end FourRootZeroGlobalSectionPoints318
