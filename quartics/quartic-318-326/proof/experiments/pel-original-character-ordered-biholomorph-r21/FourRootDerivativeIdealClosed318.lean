module
public import FourRootGluedDerivativeIdeal318
public import FourRootProjectiveChartPullbacks318
public import FourRootWholeSchemeGeometry318
public import QuotientOpenRange318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace FourRootDerivativeIdealClosed318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FourRootDerivativeZeroIdeals318 FourRootGluedDerivativeIdeal318
variable (b:Fin 4→ℂ)
lemma finite_preimage:into b ⁻¹ᵁ(FourRootGluedScheme318.finiteChart b).opensRange=
    (finiteChart b).opensRange:=by
  ext x
  constructor
  · intro hx
    rcases charts_cover b x with ⟨a,rfl⟩|⟨a,rfl⟩
    · exact ⟨a,rfl⟩
    · have ha:a∈(toInfinity b).opensRange:=by
        rw [show (toInfinity b).opensRange=
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal b)))) ⁻¹ᵁ
          (FourRootGluedScheme318.intoInfinity b).opensRange from
            QuotientOpenRange318.range (infinityArrow b) _ _ rfl]
        rw [←FourRootProjectiveChartPullbacks318.infinity_preimage_finite]
        change infinityInto b a∈(FourRootGluedScheme318.finiteChart b).opensRange
        change into b (infinityChart b a)∈_ at hx
        rw [←Scheme.Hom.comp_apply,infinityChart_into] at hx
        exact hx
      obtain ⟨z,hz⟩:=ha
      refine ⟨toFinite b z,?_⟩
      change (toFinite b≫finiteChart b) z=_
      rw [pushout.condition]
      change infinityChart b (toInfinity b z)=_
      rw [hz]
  · rintro ⟨a,rfl⟩
    change into b (finiteChart b a)∈_
    rw [←Scheme.Hom.comp_apply,finiteChart_into]
    exact ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal b))) a,rfl⟩
lemma infinity_preimage:into b ⁻¹ᵁ(FourRootGluedScheme318.infinityChart b).opensRange=
    (infinityChart b).opensRange:=by
  ext x
  constructor
  · intro hx
    rcases charts_cover b x with ⟨a,rfl⟩|⟨a,rfl⟩
    · have ha:a∈(toFinite b).opensRange:=by
        rw [show (toFinite b).opensRange=
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal b)))) ⁻¹ᵁ
          (Spec.map (finiteArrow b)).opensRange from
            QuotientOpenRange318.range (finiteArrow b) _ _ (ideal_transition b).symm]
        rw [finiteArrow,←FourRootGluedScheme318.intoFinite_eq,
          ←FourRootProjectiveChartPullbacks318.finite_preimage_infinity]
        change finiteInto b a∈(FourRootGluedScheme318.infinityChart b).opensRange
        change into b (finiteChart b a)∈_ at hx
        rw [←Scheme.Hom.comp_apply,finiteChart_into] at hx
        exact hx
      obtain ⟨z,hz⟩:=ha
      refine ⟨toInfinity b z,?_⟩
      change (toInfinity b≫infinityChart b) z=_
      rw [←pushout.condition]
      change finiteChart b (toFinite b z)=_
      rw [hz]
    · exact ⟨a,rfl⟩
  · rintro ⟨a,rfl⟩
    change into b (infinityChart b a)∈_
    rw [←Scheme.Hom.comp_apply,infinityChart_into]
    exact ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal b))) a,rfl⟩
lemma finite_square:IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal b)))) (finiteChart b)
    (FourRootGluedScheme318.finiteChart b) (into b):=
  IsOpenImmersion.isPullback _ _ _ _ (finiteChart_into b) (finite_preimage b)
lemma infinity_square:IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal b)))) (infinityChart b)
    (FourRootGluedScheme318.infinityChart b) (into b):=
  IsOpenImmersion.isPullback _ _ _ _ (infinityChart_into b) (infinity_preimage b)
/-- The glued literal principal quotient charts are the ENTIRE actual
base changes and give a genuine global closed immersion. No radical is
taken and no equality only on complex points is used. -/
instance closed:IsClosedImmersion (into b):=by
  apply IsZariskiLocalAtTarget.of_openCover (FourRootWholeSchemeGeometry318.twoChartCover b)
  intro i
  cases i
  · have h:=(infinity_square b).flip
    haveI:IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal b)))):=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hc:IsClosedImmersion (h.isoPullback.inv≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal b)))):=inferInstance
    simpa only [h.isoPullback_inv_snd] using hc
  · have h:=(finite_square b).flip
    haveI:IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal b)))):=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hc:IsClosedImmersion (h.isoPullback.inv≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal b)))):=inferInstance
    simpa only [h.isoPullback_inv_snd] using hc
/-- Actual ideal-sheaf data of the constructed closed subscheme. Local
identification with the derivative and trace different is proved after
this construction, not substituted into its definition. -/
@[expose] def idealSheaf:(FourRootGluedScheme318.scheme b).IdealSheafData:=(into b).ker
@[expose] def subschemeIso:zeroScheme b≅(idealSheaf b).subscheme:=asIso (into b).toImage
@[reassoc] lemma subschemeIso_into:(subschemeIso b).hom≫(idealSheaf b).subschemeι=into b:=
  (into b).toImage_imageι
end FourRootDerivativeIdealClosed318
