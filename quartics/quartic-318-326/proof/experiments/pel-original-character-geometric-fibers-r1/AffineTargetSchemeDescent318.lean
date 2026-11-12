module
public import AffineTargetCoordinates318
public section
noncomputable section
namespace AffineTargetSchemeDescent318
open AlgebraicGeometry CategoryTheory
open AffineTargetCoordinates318
universe u
variable {X Y:Scheme.{u}} {R:Type u} [CommRing R]

/-- The global ring-map universal property yields an ACTUAL scheme-map
factorization for affine targets, without claiming arbitrary targets. -/
theorem existsUnique_factor (f:X⟶Y) (g:X⟶Spec (CommRingCat.of R))
    (h:∃!k:R→+*Γ(Y,⊤),f.appTop.hom.comp k=coordinates g):
    ∃!k:Y⟶Spec (CommRingCat.of R),f≫k=g:=by
  obtain ⟨k,hk,hu⟩:=h
  refine ⟨fromCoordinates k,?_,?_⟩
  · apply coordinates_injective
    rw [coordinates_comp,coordinates_fromCoordinates]
    exact hk
  · intro l hl
    apply coordinates_injective
    rw [coordinates_fromCoordinates]
    apply hu
    rw [←coordinates_comp,hl]

/-- Conversely every affine-target factorization has precisely the old
coordinate factorization. No alternate affine coordinate choice is made. -/
lemma factor_iff_coordinates (f:X⟶Y) (g:X⟶Spec (CommRingCat.of R))
    (k:Y⟶Spec (CommRingCat.of R)):
    f≫k=g ↔ f.appTop.hom.comp (coordinates k)=coordinates g:=by
  rw [←coordinates_comp]
  exact ⟨congrArg coordinates,coordinates_injective⟩
end AffineTargetSchemeDescent318
