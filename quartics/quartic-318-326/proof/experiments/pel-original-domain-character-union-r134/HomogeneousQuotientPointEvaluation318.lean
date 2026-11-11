module
public import HomogeneousQuotientChart318
public section
noncomputable section
namespace HomogeneousQuotientPointEvaluation318
open HomogeneousQuotientChart318 ComplexProjectiveMarkerPoint318
variable {ι:Type*}(I:Ideal (Equations (ι:=ι)))(v:ι→ℂ)
    (hI:∀p∈I,MvPolynomial.eval v p=0)(j:ι)(hj:v j≠0)
@[expose] def quotientEvaluation:QuotientRing I→+*ℂ:=
  Ideal.Quotient.lift I (MvPolynomial.eval₂Hom (RingHom.id ℂ) v) hI
lemma quotientEvaluation_mk(p:Equations (ι:=ι)):
    quotientEvaluation I v hI (Ideal.Quotient.mk I p)=MvPolynomial.eval v p:=rfl
lemma units(y:Submonoid.powers (Ideal.Quotient.mk I (MvPolynomial.X j))):
    IsUnit (quotientEvaluation I v hI y):=by
  obtain ⟨y,⟨n,rfl⟩⟩:=y
  rw [map_pow,quotientEvaluation_mk,MvPolynomial.eval_X]
  exact (isUnit_iff_ne_zero.mpr hj).pow n
@[expose] def localizationEvaluation:LocalizedQuotient I j→+*ℂ:=
  IsLocalization.lift (units I v hI j hj)
@[expose] def evaluation:degreeZero I j→+*ℂ:=
  (localizationEvaluation I v hI j hj).comp (degreeZero I j).subtype
lemma fraction_evaluation(n:ℕ)(p:Equations (ι:=ι))(hp:p.IsHomogeneous n):
    evaluation I v hI j hj ((quotientMap I j).rangeRestrict (fraction j n p hp))=
      MvPolynomial.eval v p/(v j)^n:=by
  change localizationEvaluation I v hI j hj (quotientMap I j (fraction j n p hp))=_
  rw [fraction_value]
  apply (IsLocalization.lift_mk'_spec (units I v hI j hj) _ _ _).mpr
  simp only [map_pow,quotientEvaluation_mk,MvPolynomial.eval_X]
  field_simp [pow_ne_zero n hj]
end HomogeneousQuotientPointEvaluation318
