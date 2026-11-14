module
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public section
noncomputable section
namespace AffineTargetCoordinates318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X Y:Scheme.{u}} {R:Type u} [CommRing R]

/-- The actual global-coordinate map of a scheme morphism to Spec R,
including the canonical Spec-global-sections comparison. -/
@[expose] def coordinates (g:X⟶Spec (CommRingCat.of R)):R→+*Γ(X,⊤):=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv≫g.appTop).hom

@[expose] def fromCoordinates (k:R→+*Γ(X,⊤)):X⟶Spec (CommRingCat.of R):=
  (ΓSpec.adjunction.homEquiv X (op (CommRingCat.of R))) (CommRingCat.ofHom k).op

@[simp] lemma coordinates_fromCoordinates (k:R→+*Γ(X,⊤)):
    coordinates (fromCoordinates k)=k:=by
  exact congrArg CommRingCat.Hom.hom
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom k))

lemma coordinates_injective:Function.Injective
    (coordinates (X:=X) (R:=R)):=by
  intro g h he
  apply AlgebraicGeometry.ext_to_Spec
  exact CommRingCat.hom_ext he

@[simp] lemma fromCoordinates_coordinates (g:X⟶Spec (CommRingCat.of R)):
    fromCoordinates (coordinates g)=g:=by
  apply coordinates_injective
  exact coordinates_fromCoordinates _

/-- Exact contravariant composition, valid for an arbitrary source and
intermediate scheme, not requiring either to be affine. -/
lemma coordinates_comp (f:X⟶Y) (g:Y⟶Spec (CommRingCat.of R)):
    coordinates (f≫g)=f.appTop.hom.comp (coordinates g):=by
  apply RingHom.ext
  intro r
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv≫(f≫g).appTop) r=_
  rw [Scheme.Hom.comp_appTop]
end AffineTargetCoordinates318
