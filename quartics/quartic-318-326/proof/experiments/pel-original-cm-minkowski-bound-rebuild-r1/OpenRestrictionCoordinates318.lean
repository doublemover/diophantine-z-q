module
public import OpenSectionAffineTargetMap318
public section
noncomputable section
namespace OpenRestrictionCoordinates318
open AlgebraicGeometry CategoryTheory AffineTargetCoordinates318
universe u
variable {X Y:Scheme.{u}}

/-- Exact normalization of an actual restricted morphism's global
coordinate map. Both native topIso factors cancel in the right order. -/
lemma resLE_coordinates_comp {R:Type u} [CommRing R] (f:X⟶Y)
    (U:Y.Opens) (W:X.Opens) (e:W≤f⁻¹ᵁU) (k:R→+*Γ(Y,U)):
    (f.resLE U W e).appTop.hom.comp (U.topIso.inv.hom.comp k)=
      W.topIso.inv.hom.comp ((f.appLE U W e).hom.comp k):=by
  apply RingHom.ext
  intro r
  change (U.topIso.inv≫(f.resLE U W e).appTop) (k r)=_
  rw [Scheme.Hom.resLE_app_top]
  simp only [Iso.inv_hom_id_assoc]

/-- The native coordinates of a restriction into a target affine open
are its actual appLE, not a newly chosen equivalent ring map. -/
lemma coordinates_resLE (g:X⟶Y) (V:Y.Opens) (W:X.Opens)
    (e:W≤g⁻¹ᵁV) (hV:IsAffineOpen V):
    coordinates (g.resLE V W e≫hV.isoSpec.hom)=
      W.topIso.inv.hom.comp (g.appLE V W e).hom:=by
  have he:(Scheme.ΓSpecIso Γ(Y,V)).inv≫(g.resLE V W e≫hV.isoSpec.hom).appTop=
      g.appLE V W e≫W.topIso.inv:=by
    rw [Scheme.Hom.comp_appTop,hV.isoSpec_hom_appTop]
    simp only [Scheme.Hom.resLE_app_top,Category.assoc,Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom he
end OpenRestrictionCoordinates318
