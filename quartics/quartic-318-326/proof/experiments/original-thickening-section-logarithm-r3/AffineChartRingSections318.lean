module
public import OpenChartSections318

public section
noncomputable section
namespace AffineChartRingSections318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A : Type u} [CommRing A]
variable (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]

/-- Original affine chart coordinates as actual regular functions on its full image. -/
@[expose] def equivalence : A ≃+ Γ(X,j ''ᵁ ⊤) :=
  ((j.appIso ⊤ ≪≫ Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv).toAddEquiv

theorem equivalence_apply (a : A) :
    equivalence j a = (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := rfl

/-- Transport only the named open, keeping the original affine section isomorphism. -/
@[expose] def equivalenceOn (U : X.Opens) (h : j ''ᵁ ⊤ = U) : A ≃+ Γ(X,U) := by
  subst U
  exact equivalence j

variable {B : Type u} [CommRing B] (f : A →+* B)
variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]

/-- Actual algebra restriction and ambient regular-section restriction agree. -/
theorem restrict_to (k : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion k]
    (route : Spec.map (CommRingCat.ofHom f) ≫ j = k)
    (h : k ''ᵁ ⊤ ≤ j ''ᵁ ⊤) (a : A) :
    X.presheaf.map (homOfLE h).op (equivalence j a) = equivalence k (f a) := by
  subst k
  exact OpenChartSections318.affine_restriction (CommRingCat.ofHom f) j a

/-- The same compatibility on any proved-equal full overlap open. -/
theorem restrict_to_on (k : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion k]
    (route : Spec.map (CommRingCat.ofHom f) ≫ j = k)
    (U : X.Opens) (hU : k ''ᵁ ⊤ = U) (h : U ≤ j ''ᵁ ⊤) (a : A) :
    X.presheaf.map (homOfLE h).op (equivalence j a) = equivalenceOn k U hU (f a) := by
  subst U
  exact restrict_to j f k route h a

end AffineChartRingSections318
