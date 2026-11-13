module
public import LineFrameTopScalar318
public import ModuleTopExt318
public section
noncomputable section
namespace SectionFrameMorphismFormula318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
  (σ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (c : Γ(X,U))
  (hc : ∀ (W : X.Opens) (hW : W≤U),σ.app W 1=
    OpenLineFrameCoordinates318.frame M U e W hW (X.presheaf.map (homOfLE hW).op c))
include hc in
/-- Exact normalized restricted MORPHISM identity from the actual
whole-subopen frame coefficients, not only a point or top-value formula. -/
lemma formula : (Scheme.Modules.restrictUnitIso U.ι).inv≫
    (Scheme.Modules.restrictFunctor U.ι).map σ=
      ClutchedModule318.multiply ((LineFrameTopScalar318.ringTop U).inv c)≫e.hom := by
  apply ModuleTopExt318.ext
  let Z := U.ι ''ᵁ (⊤ : U.toScheme.Opens)
  change σ.app Z ((U.ι.appIso ⊤).inv 1)=
    e.hom.app ⊤ ((ClutchedModule318.multiply ((LineFrameTopScalar318.ringTop U).inv c)).app ⊤ 1)
  rw [map_one,ClutchedModule318.multiply_top,one_mul]
  rw [hc Z (LineFrameTopScalar318.image_top U).le]
  have hr : X.presheaf.map (homOfLE (LineFrameTopScalar318.image_top U).le).op c=
      (LineFrameTopScalar318.ringTop U).inv c := by rfl
  rw [hr]
  exact LineFrameTopScalar318.over_hom_app M U e ⊤ _
include hc in
lemma restriction_formula : (Scheme.Modules.restrictFunctor U.ι).map σ=
    (Scheme.Modules.restrictUnitIso U.ι).hom≫
      ClutchedModule318.multiply ((LineFrameTopScalar318.ringTop U).inv c)≫e.hom := by
  rw [←formula M U e σ c hc,Iso.hom_inv_id_assoc]
end SectionFrameMorphismFormula318
