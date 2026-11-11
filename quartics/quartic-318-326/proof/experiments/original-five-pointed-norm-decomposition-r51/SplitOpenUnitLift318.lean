module
public import UnitCocycleTwist318
public section
noncomputable section
namespace SplitOpenUnitLift318
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) (r : X ⟶ X₀) (hr : i ≫ r = 𝟙 X₀)
    (W : X.Opens) (hW : W ≤ r ⁻¹ᵁ (i ⁻¹ᵁ W))
/-- Actual first-projection lifting on an entire stable open. -/
@[expose] def ringLift : Γ(X₀,i ⁻¹ᵁ W) →+* Γ(X,W) := (r.appLE (i ⁻¹ᵁ W) W hW).hom
include hr in
lemma reduction_lift (a : Γ(X₀,i ⁻¹ᵁ W)) : i.app W (ringLift i r W hW a) = a := by
  change (r.appLE (i ⁻¹ᵁ W) W hW ≫ i.app W) a = a
  rw [i.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hr]
  all_goals
    change ((𝟙 (Γ(X₀,i ⁻¹ᵁ W))) ≫ X₀.presheaf.map (𝟙 (op (i ⁻¹ᵁ W)))) a = a
    rw [X₀.presheaf.map_id, Category.comp_id]
    all_goals rfl
@[expose] def unitLift : Γ(X₀,i ⁻¹ᵁ W)ˣ →* Γ(X,W)ˣ := Units.map (ringLift i r W hW).toMonoidHom
include hr in
lemma reduction_unit (a : Γ(X₀,i ⁻¹ᵁ W)ˣ) :
    Units.map (i.app W).hom.toMonoidHom (unitLift i r W hW a) = a := by
  apply Units.ext
  exact reduction_lift i r hr W hW a.val
variable {V W : X.Opens} (h : W ≤ V)
    (hV : V ≤ r ⁻¹ᵁ (i ⁻¹ᵁ V)) (hW : W ≤ r ⁻¹ᵁ (i ⁻¹ᵁ W))
lemma natural (a : Γ(X₀,i ⁻¹ᵁ V)) :
    X.presheaf.map (homOfLE h).op (ringLift i r V hV a) =
      ringLift i r W hW (X₀.presheaf.map (homOfLE (i.preimage_mono h)).op a) := by
  change (r.appLE (i ⁻¹ᵁ V) V hV ≫ X.presheaf.map (homOfLE h).op) a =
    (X₀.presheaf.map (homOfLE (i.preimage_mono h)).op ≫ r.appLE (i ⁻¹ᵁ W) W hW) a
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
lemma unit_natural (a : Γ(X₀,i ⁻¹ᵁ V)ˣ) :
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom (unitLift i r V hV a) =
      unitLift i r W hW (Units.map (X₀.presheaf.map (homOfLE (i.preimage_mono h)).op).hom.toMonoidHom a) := by
  apply Units.ext
  exact natural i r h hV hW a.val
end SplitOpenUnitLift318
