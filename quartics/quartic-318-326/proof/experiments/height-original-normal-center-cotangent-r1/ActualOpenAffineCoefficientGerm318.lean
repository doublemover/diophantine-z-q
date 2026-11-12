module
public import ActualOpenAffineStalkFraction318
public section
noncomputable section
namespace ActualOpenAffineCoefficientGerm318
open AlgebraicGeometry CategoryTheory
universe u
variable {X:Scheme.{u}} [IsIntegral X] {R:Type u} [CommRing R] [IsDomain R]
    (j:Spec (CommRingCat.of R)⟶X) [IsOpenImmersion j]
    (p:PrimeSpectrum R) [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)]
@[expose] def domain:X.Opens:=j ''ᵁ ⊤
lemma point_mem:j p∈domain j:=⟨p,trivial,rfl⟩
local instance nonempty_domain:Nonempty (domain j):=⟨⟨j p,point_mem j p⟩⟩
/-- The actual original affine coefficient, as a section on the image
of the genuine original open immersion. -/
@[expose] def chartSection(r:R):Γ(X,domain j):=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
lemma local_coefficient(r:R):
    ActualOpenAffineDvr318.localEquivalence j p
      (X.presheaf.germ (domain j) (j p) (point_mem j p) (chartSection j r))=
      algebraMap R (Localization.AtPrime p.asIdeal) r:=by
  let i:⊤⟶j ⁻¹ᵁ (domain j):=eqToHom (Scheme.Hom.preimage_image_eq j ⊤).symm
  have hi:(Spec (CommRingCat.of R)).presheaf.map i.op
      (j.app (domain j) (chartSection j r))=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv r:=by
    change ((j.app (domain j)≫(Spec (CommRingCat.of R)).presheaf.map i.op)
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)))=_
    rw [←Scheme.Hom.appIso_hom]
    exact Iso.inv_hom_id_apply (j.appIso ⊤) _
  have hg:(Spec (CommRingCat.of R)).presheaf.germ (j ⁻¹ᵁ domain j) p (point_mem j p)
      (j.app (domain j) (chartSection j r))=
      (Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r):=by
    rw [←hi]
    exact ((Spec (CommRingCat.of R)).presheaf.germ_res_apply i p trivial
      (j.app (domain j) (chartSection j r))).symm
  change (Spec.stalkIso (CommRingCat.of R) p).hom
    (j.stalkMap p (X.presheaf.germ (domain j) (j p) (point_mem j p) (chartSection j r)))=_
  rw [j.germ_stalkMap_apply,hg]
  have h:=ConcreteCategory.congr_hom (Spec.germ_stalkMapIso_hom (CommRingCat.of R) p)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  simpa only [CommRingCat.comp_apply,Iso.inv_hom_id_apply] using h
/-- The field comparison is pinned on every original affine coefficient,
not merely as an abstract isomorphism of fraction fields. -/
theorem fraction_coefficient(r:R):
    ActualOpenAffineStalkFraction318.comparison j p
      (X.germToFunctionField (domain j) (chartSection j r))=
      algebraMap R (FractionRing R) r:=by
  rw [ActualOpenAffineStalkFraction318.on_section j p (domain j) (point_mem j p),
    local_coefficient]
  exact ActualPrimeMeromorphicOrder318.on_source R p.asIdeal r
end ActualOpenAffineCoefficientGerm318
