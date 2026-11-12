module
public import AffineTargetCoordinates318
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace OpenSectionAffineTargetMap318
open AlgebraicGeometry CategoryTheory AffineTargetCoordinates318
universe u
variable {X Z:Scheme.{u}} (U:X.Opens) {V:Z.Opens} (hV:IsAffineOpen V)

/-- A map of the ACTUAL open section rings creates a genuine morphism
of open schemes whenever the target open is affine. The source open need
not be affine; its exact topIso is retained in the coordinate formula. -/
@[expose] def toAffineOpen (k:Γ(Z,V)→+*Γ(X,U)):U.toScheme⟶V.toScheme:=
  fromCoordinates (U.topIso.inv.hom.comp k)≫hV.isoSpec.inv

lemma coordinates_toAffineOpen (k:Γ(Z,V)→+*Γ(X,U)):
    coordinates (toAffineOpen U hV k≫hV.isoSpec.hom)=U.topIso.inv.hom.comp k:=by
  unfold toAffineOpen
  rw [Category.assoc,hV.isoSpec.inv_hom_id,Category.comp_id,coordinates_fromCoordinates]

@[expose] def toTarget (k:Γ(Z,V)→+*Γ(X,U)):U.toScheme⟶Z:=
  toAffineOpen U hV k≫V.ι

/-- Equality of constructed local morphisms follows from equality of
the original section-ring maps, with no chosen coordinate basis. -/
lemma toAffineOpen_injective:Function.Injective (toAffineOpen U hV):=by
  intro k l he
  have hh:=congrArg (fun f:U.toScheme⟶V.toScheme=>coordinates (f≫hV.isoSpec.hom)) he
  rw [coordinates_toAffineOpen,coordinates_toAffineOpen] at hh
  apply RingHom.ext
  intro r
  exact (ConcreteCategory.bijective_of_isIso U.topIso.inv).1 (RingHom.congr_fun hh r)
end OpenSectionAffineTargetMap318
