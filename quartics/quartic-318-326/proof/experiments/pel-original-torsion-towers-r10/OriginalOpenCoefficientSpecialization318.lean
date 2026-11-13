module
public import GlobalSectionFrameCocycle318
public import Mathlib.AlgebraicGeometry.Restrict
public section
noncomputable section
namespace OriginalOpenCoefficientSpecialization318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (U W : X.Opens) (h : W ≤ U)

/-- The actual original-open section comparison commutes with literal
restriction between open subschemes. No unnamed coefficient-ring
identification is inserted into point specialization. -/
lemma restriction_square (r : Γ(U.toScheme,⊤)) :
    (LineFrameTopScalar318.ringTop W).hom ((X.homOfLE h).appTop r) =
      GlobalSectionFrameCoordinates318.coefficient U r W h := by
  simp only [GlobalSectionFrameCoordinates318.coefficient,LineFrameTopScalar318.ringTop_hom,
    Scheme.homOfLE_appTop,←ConcreteCategory.comp_apply,←Functor.map_comp]
  rfl

/-- A ring map out of the original overlap ring has exactly the same
value as the actual pulled-back regular function on the open scheme. -/
lemma coefficient_pullback (r : Γ(U.toScheme,⊤)) :
    (LineFrameTopScalar318.ringTop W).inv
      (GlobalSectionFrameCoordinates318.coefficient U r W h) = (X.homOfLE h).appTop r := by
  rw [←restriction_square U W h r]
  exact Iso.hom_inv_id_apply _ _

/-- Exact specialization through a genuine scheme point over ANY same-universe ring, keeping the
Γ(Spec K) comparison explicit on both sides. -/
lemma point_value {K : Type u} [CommRing K] (r : Γ(U.toScheme,⊤))
    (p : Spec (CommRingCat.of K) ⟶ W.toScheme) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (p.appTop ((LineFrameTopScalar318.ringTop W).inv
        (GlobalSectionFrameCoordinates318.coefficient U r W h))) =
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((p ≫ X.homOfLE h).appTop r) := by
  rw [coefficient_pullback]
  rfl
end OriginalOpenCoefficientSpecialization318
