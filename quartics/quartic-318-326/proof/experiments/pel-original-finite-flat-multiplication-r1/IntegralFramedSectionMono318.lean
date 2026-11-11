module
public import OpenLineFrameCoordinates318
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace IntegralFramedSectionMono318
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} [IsIntegral X] (M : X.Modules)
  (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (U : X.Opens) [Nonempty U]
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
  (c : Γ(X,U)) (hc : c≠0)
  (hφ : ∀ (V : X.Opens) (hV : V≤U) (r : Γ(X,V)),φ.app V r=
    OpenLineFrameCoordinates318.frame M U e V hV (r*X.presheaf.map (homOfLE hV).op c))

include hc hφ in
lemma app_injective (W : X.Opens) : Function.Injective (φ.app W) := by
  rcases (W : Set X).eq_empty_or_nonempty with hW | hW
  · have he : W=⊥ := SetLike.ext' hW
    subst W
    exact fun _ _ _ => Subsingleton.elim _ _
  · obtain ⟨x,hx⟩ := nonempty_preirreducible_inter W.isOpen U.isOpen hW
      (by obtain ⟨y⟩ := ‹Nonempty U›; exact ⟨y,y.property⟩)
    let V := W⊓U
    letI : Nonempty V := ⟨⟨x,hx⟩⟩
    letI : IsDomain Γ(X,V) := IsIntegral.component_integral V
    have hcv : X.presheaf.map (homOfLE (show V≤U from inf_le_right)).op c≠0 := by
      intro h
      exact hc (map_injective_of_isIntegral X (homOfLE inf_le_right) (h.trans (map_zero _).symm))
    intro r s h
    have hr := congrArg (fun f => f r) (φ.mapPresheaf.naturality (homOfLE (show V≤W from inf_le_left)).op)
    have hs := congrArg (fun f => f s) (φ.mapPresheaf.naturality (homOfLE (show V≤W from inf_le_left)).op)
    change φ.app V (X.presheaf.map (homOfLE inf_le_left).op r)=
      M.presheaf.map (homOfLE inf_le_left).op (φ.app W r) at hr
    change φ.app V (X.presheaf.map (homOfLE inf_le_left).op s)=
      M.presheaf.map (homOfLE inf_le_left).op (φ.app W s) at hs
    have he := hr.trans ((congrArg (M.presheaf.map (homOfLE (show V≤W from inf_le_left)).op) h).trans hs.symm)
    rw [hφ V inf_le_right,hφ V inf_le_right] at he
    have hm := (OpenLineFrameCoordinates318.frame M U e V inf_le_right).injective he
    exact map_injective_of_isIntegral X (homOfLE (show V≤W from inf_le_left))
      (mul_right_cancel₀ hcv hm)

include hc hφ in
lemma mono : Mono φ where
  right_cancellation := by
    intro N f g h
    apply Scheme.Modules.hom_ext
    intro V
    ext s
    apply app_injective M φ U e c hc hφ V
    exact congrArg (fun ψ => ψ.app V s) h
end IntegralFramedSectionMono318
