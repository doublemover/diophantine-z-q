module
public import PELOriginalCandidateAffineCharts318
public section
noncomputable section
namespace PELOriginalCandidateChartSections318
open AlgebraicGeometry CategoryTheory
open PELOriginalCandidateAffineCharts318 PELOriginalCubicRelationIdeal318
open PELOriginalLevelTheta318 HomogeneousQuotientChart318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)

/-- The actual global sections of the original inverse-image affine chart,
not an abstract ring merely having the same prime points. -/
@[expose] def coordinates:
    Γ((candidateChart τ hτ j).toScheme,⊤)≃+*CoordinateChart τ hτ j:=
  (Scheme.Γ.mapIso (actualChartIso τ hτ j).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).commRingCatIsoToRingEquiv

/-- Restrict an ACTUAL ambient homogeneous chart function through the
original candidate closed immersion. -/
@[expose] def restriction(a:Chart j):Γ((candidateChart τ hτ j).toScheme,⊤):=
  (toChart τ hτ j).appTop ((Scheme.ΓSpecIso (CommRingCat.of (Chart j))).inv a)
lemma coordinates_restriction(a:Chart j):
    coordinates τ hτ j (restriction τ hτ j a)=
      (quotientMap (relations τ hτ) j).rangeRestrict a:=by
  change (Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom
    (((toChart τ hτ j).appTop≫(actualChartIso τ hτ j).hom.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of (Chart j))).inv a))=_
  rw [←Scheme.Hom.comp_appTop,actualChartIso_over]
  have hn:=congrArg (fun f=>f a) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (quotientMap (relations τ hτ) j).rangeRestrict))
  rw [←hn]
  exact Iso.inv_hom_id_apply _ _

/-- Every actual section has a matching-degree homogeneous numerator in
the original polynomial ring. Thus the chart comparison is exhaustive
on sections as well as on prime points and sheaves. -/
lemma section_normal_form(s:Γ((candidateChart τ hτ j).toScheme,⊤)):
    ∃n p (hp:p.IsHomogeneous n),
      (coordinates τ hτ j s).val=
        IsLocalization.mk' (LocalizedQuotient (relations τ hτ) j)
          (Ideal.Quotient.mk (relations τ hτ) p)
          ⟨Ideal.Quotient.mk (relations τ hτ) (MvPolynomial.X j)^n,⟨n,rfl⟩⟩:=
  degreeZero_normal_form (relations τ hτ) j (coordinates τ hτ j s)

/-- Literal X_i/X_j, restricted via the SAME ambient affine chart map. -/
@[expose] def ratioSection(i:Label 3):Γ((candidateChart τ hτ j).toScheme,⊤):=
  restriction τ hτ j (fraction j 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i))
lemma ratioSection_value(i:Label 3):
    (coordinates τ hτ j (ratioSection τ hτ j i)).val=
      IsLocalization.mk' (LocalizedQuotient (relations τ hτ) j)
        (Ideal.Quotient.mk (relations τ hτ) (MvPolynomial.X i))
        ⟨Ideal.Quotient.mk (relations τ hτ) (MvPolynomial.X j)^1,⟨1,rfl⟩⟩:=by
  rw [ratioSection,coordinates_restriction]
  exact fraction_value (relations τ hτ) j 1 (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i)

/-- The original restricted homogeneous fraction vanishes exactly when
some genuine denominator power kills its numerator modulo the original
relation ideal. No domain or cancellation hypothesis is smuggled in. -/
lemma restriction_fraction_zero_iff(n:ℕ)(p:Equations)(hp:p.IsHomogeneous n):
    restriction τ hτ j (fraction j n p hp)=0↔
      ∃k:ℕ,(MvPolynomial.X j)^k*p∈relations τ hτ:=by
  rw [←(coordinates τ hτ j).map_eq_zero_iff,coordinates_restriction]
  have hzero:((quotientMap (relations τ hτ) j).rangeRestrict
      (fraction j n p hp)=0)↔quotientMap (relations τ hτ) j (fraction j n p hp)=0:=by
    constructor
    · exact fun h=>congrArg Subtype.val h
    · exact fun h=>Subtype.ext h
  exact hzero.trans (fraction_zero_iff (relations τ hτ) j n p hp)
end PELOriginalCandidateChartSections318
