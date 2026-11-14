module
public import StableOpenSectionPullback318
public section
noncomputable section
namespace StableOpenSectionLaws318
open AlgebraicGeometry CategoryTheory StableOpenSectionPullback318
universe u
variable {X:Scheme.{u}}

lemma sectionPullback_congr {f g:X⟶X} (e:f=g) (U:X.Opens)
    (hf:U≤f⁻¹ᵁU) (hg:U≤g⁻¹ᵁU):
    sectionPullback f U hf=sectionPullback g U hg:=by
  subst g
  rfl

/-- Exact contravariant appLE composition on the SAME stable open.
Proofs of stability are irrelevant, but the morphisms are not replaced. -/
lemma sectionPullback_comp (f g:X⟶X) (U:X.Opens)
    (hf:U≤f⁻¹ᵁU) (hg:U≤g⁻¹ᵁU) (hfg:U≤(f≫g)⁻¹ᵁU):
    sectionPullback (f≫g) U hfg=
      (sectionPullback f U hf).comp (sectionPullback g U hg):=by
  exact (congrArg CommRingCat.Hom.hom
    (Scheme.Hom.appLE_comp_appLE f g U U U hg hf)).symm

lemma sectionPullback_id (U:X.Opens) (h:U≤(𝟙 X)⁻¹ᵁU):
    sectionPullback (𝟙 X) U h=RingHom.id Γ(X,U):=by
  simp [sectionPullback,Scheme.Hom.appLE]
end StableOpenSectionLaws318
