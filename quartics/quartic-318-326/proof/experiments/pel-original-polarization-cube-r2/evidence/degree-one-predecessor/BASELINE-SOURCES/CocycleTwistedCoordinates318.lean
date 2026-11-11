module
public import CocycleOverlapCoordinates318
public section
noncomputable section
namespace CocycleTwistedCoordinates318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CocycleLocalCoefficients318 CocycleOverlapCoordinates318
set_option maxHeartbeats 450000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
lemma twisted_app {Y₀ Y₁ W:Scheme.{u}} (j₀:Y₀⟶X) (j₁:Y₁⟶X)
    (k₀:W⟶Y₀) (k₁:W⟶Y₁) (h:k₁≫j₁=k₀≫j₀)
    (a:Γ(W,⊤)) (V:X.Opens)
    (e:(k₀≫j₀)⁻¹ᵁV=(k₁≫j₁)⁻¹ᵁV) (x:Γ(Y₁,j₁⁻¹ᵁV)):
    (ClutchedModule318.twistedRestriction j₀ j₁ k₀ k₁ h a).app V x=
      W.presheaf.map (eqToHom e).op (k₁.app (j₁⁻¹ᵁV) x)*
        W.presheaf.map (homOfLE (show (k₀≫j₀)⁻¹ᵁV≤⊤ from le_top)).op a:=by
  exact ClutchedModule318.multiply_apply a ((k₀≫j₀)⁻¹ᵁV)
    (W.presheaf.map (eqToHom e).op (k₁.app (j₁⁻¹ᵁV) x))
lemma right_coordinate (i j k:ι) (a:Γ(X,U k⊓U i)):
    (overlapIso U i j k).hom ((localRight U c i j k).app ⊤ ((coefficientIso U i k).inv a))=
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op a *
        X.presheaf.map (homOfLE inf_le_left).op (c.transition j k).val:=by
  change (overlapIso U i j k).hom
    ((ClutchedModule318.twistedRestriction (U j).ι (U k).ι
      (OpenClutchedLine318.leftInclusion (U j) (U k))
      (OpenClutchedLine318.rightInclusion (U j) (U k))
      (OpenClutchedLine318.square (U j) (U k))
      (OpenClutchedLine318.transition (U j) (U k) (c.transition j k))).app
      ((U i).ι ''ᵁ ⊤) ((coefficientIso U i k).inv a))=_
  rw [twisted_app _ _ _ _ _ _ _ (by rw [OpenClutchedLine318.square])]
  rw [map_mul]
  congr 1
  · simp only [overlapIso,coefficientIso,Functor.mapIso_hom,Functor.mapIso_inv,
      OpenClutchedLine318.rightInclusion,Scheme.homOfLE_app,
      Scheme.Opens.toScheme_presheaf_map]
    change ((X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) : _⟶_) a=_
    simp only [←Functor.map_comp]
    rfl
  · simp only [overlapIso,Functor.mapIso_hom,
      OpenClutchedLine318.transition,Scheme.Opens.topIso_inv,
      Scheme.Opens.toScheme_presheaf_map]
    change ((X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) : _⟶_) (c.transition j k).val=_
    simp only [←Functor.map_comp]
    rfl
end CocycleTwistedCoordinates318
