module
public import OpenRestrictionCoordinates318
public section
noncomputable section
namespace OpenAffineTargetFactorization318
open AlgebraicGeometry CategoryTheory AffineTargetCoordinates318
open OpenSectionAffineTargetMap318 OpenRestrictionCoordinates318
universe u
variable {X Y Z:Scheme.{u}}

/-- A literal section-ring factor square yields the ACTUAL restricted
scheme factor square into an affine target open, without quotient assumptions. -/
theorem resLE_factor (f:X⟶Y) (g:X⟶Z) (U:Y.Opens) (V:Z.Opens)
    (hV:IsAffineOpen V) (e:f⁻¹ᵁU≤g⁻¹ᵁV) (k:Γ(Z,V)→+*Γ(Y,U))
    (hk:(f.app U).hom.comp k=(g.appLE V (f⁻¹ᵁU) e).hom):
    f.resLE U (f⁻¹ᵁU) le_rfl≫toAffineOpen U hV k=g.resLE V (f⁻¹ᵁU) e:=by
  apply (cancel_mono hV.isoSpec.hom).mp
  apply coordinates_injective
  rw [Category.assoc,coordinates_comp,coordinates_toAffineOpen,
    resLE_coordinates_comp,coordinates_resLE]
  simpa only [Scheme.Hom.appLE_eq_app] using
    congrArg (fun t:Γ(Z,V)→+*Γ(X,f⁻¹ᵁU)=>(f⁻¹ᵁU).topIso.inv.hom.comp t) hk

/-- The same equality after inclusion into the original arbitrary target. -/
theorem target_factor (f:X⟶Y) (g:X⟶Z) (U:Y.Opens) (V:Z.Opens)
    (hV:IsAffineOpen V) (e:f⁻¹ᵁU≤g⁻¹ᵁV) (k:Γ(Z,V)→+*Γ(Y,U))
    (hk:(f.app U).hom.comp k=(g.appLE V (f⁻¹ᵁU) e).hom):
    f.resLE U (f⁻¹ᵁU) le_rfl≫toTarget U hV k=(f⁻¹ᵁU).ι≫g:=by
  unfold toTarget
  rw [←Category.assoc,resLE_factor f g U V hV e k hk,Scheme.Hom.resLE_comp_ι]
end OpenAffineTargetFactorization318
