module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section
namespace OpenFunctionField318
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsOpenImmersion f]
  [IrreducibleSpace X] [IrreducibleSpace Y]

/-- The actual generic stalk isomorphism induced by an open immersion. -/
@[expose] def fieldIso : Y.functionField ≅ X.functionField :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq
    (genericPoint_eq_of_isOpenImmersion f))).symm ≪≫
      asIso (f.stalkMap (genericPoint X))

@[expose] def fieldEquiv : Y.functionField ≃+* X.functionField :=
  CategoryTheory.Iso.commRingCatIsoToRingEquiv (fieldIso f)

@[expose] def affineFractionEquiv (R:CommRingCat.{u}) [IsDomain R] :
    (Spec R).functionField ≃ₐ[R] FractionRing R :=
  IsLocalization.algEquiv R⁰ _ _

@[expose] def openFractionEquiv {R:CommRingCat.{u}} [IsDomain R]
    (g:Spec R⟶Y) [IsOpenImmersion g] : Y.functionField ≃+* FractionRing R :=
  (fieldEquiv g).trans (affineFractionEquiv R).toRingEquiv

/-- Exact compatibility with actual section germs, not an abstract field
isomorphism chosen independently of the source embedding. -/
theorem fieldIso_germ (U:Y.Opens) [Nonempty U] [Nonempty (f⁻¹ᵁU)] :
    Y.germToFunctionField U ≫ (fieldIso f).hom =
      f.app U ≫ X.germToFunctionField (f⁻¹ᵁU) := by
  dsimp only [fieldIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [←Category.assoc]
  change (Y.presheaf.germ U (genericPoint Y) _ ≫
      (Y.presheaf.stalkCongr _).inv) ≫ _ = _
  rw [TopCat.Presheaf.stalkCongr_inv]
  rw [Y.presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint X) _
end OpenFunctionField318
