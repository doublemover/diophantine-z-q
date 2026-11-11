module
public import PELOriginalProjectedPrimitivePolynomial318
public import FractionSeparablePolynomialOpen318
public section
noncomputable section
namespace PELOriginalPrimitiveSeparableOpen318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
open PELOriginalProjectedPrimitivePolynomial318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)(x:ComplexVectors)(hx:value τ hτ 3 j x≠0)
local instance chartDomain:IsDomain (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
abbrev PolynomialBase:=MvPolynomial (Fin 2) ℂ
abbrev RationalBase:=FractionRing PolynomialBase
/-- The SAME primitive equation, now expressed in the literal two
original projected rational variables through their proved equivalence. -/
@[expose] def rationalEquation:Polynomial RationalBase:=
  (equation τ hτ j x hx).map (rationalEquivalence τ hτ j x hx).symm.toRingHom
lemma original_equation:
    (rationalEquation τ hτ j x hx).map (rationalEquivalence τ hτ j x hx).toRingHom=
      equation τ hτ j x hx:=by
  ext n
  simp only [rationalEquation,Polynomial.coeff_map]
  exact (rationalEquivalence τ hτ j x hx).apply_symm_apply _
lemma rational_monic:(rationalEquation τ hτ j x hx).Monic:=
  (equation_monic τ hτ j x hx).map _
lemma rational_separable:(rationalEquation τ hτ j x hx).Separable:=
  (equation_separable τ hτ j x hx).map
lemma rational_degree:(rationalEquation τ hτ j x hx).natDegree=
    Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j):=by
  exact (Polynomial.natDegree_map_eq_of_injective
    (rationalEquivalence τ hτ j x hx).symm.injective _).trans (actual_degree τ hτ j x hx)

/-- A produced NONZERO polynomial in the two original base coordinates
supports a monic primitive equation with its full derivative Bezout
identity. Mapping its coefficients back gives exactly the old equation.
No assertion about equality of the resulting monogenic order with the
whole finite candidate chart is made here. -/
theorem exists_separable_open:
    ∃d:PolynomialBase,∃hd:d≠0,∃Q A B:Polynomial (Localization.Away d),
      Q.map (FractionFiniteCoefficientLift318.toField PolynomialBase RationalBase d hd)=
        rationalEquation τ hτ j x hx ∧
      Q.Monic ∧ A*Q+B*Q.derivative=1 ∧
      Q.natDegree=Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j):=by
  obtain ⟨d,hd,Q,A,B,hQ,hm,hAB⟩:=FractionSeparablePolynomialOpen318.exists_open
    PolynomialBase RationalBase (rationalEquation τ hτ j x hx)
    (rational_monic τ hτ j x hx) (rational_separable τ hτ j x hx)
  refine ⟨d,hd,Q,A,B,hQ,hm,hAB,?_⟩
  have hn:=Polynomial.natDegree_map_eq_of_injective
    (FractionFiniteCoefficientLift318.toField_injective PolynomialBase RationalBase d hd) Q
  rw [hQ,rational_degree] at hn
  exact hn.symm

/-- The lifted equation still annihilates the SAME actual primitive
field element after the exact original rational-coordinate comparison. -/
theorem lifted_original_root {d:PolynomialBase}(hd:d≠0)
    (Q:Polynomial (Localization.Away d))
    (hQ:Q.map (FractionFiniteCoefficientLift318.toField PolynomialBase RationalBase d hd)=
      rationalEquation τ hτ j x hx):
    Polynomial.aeval (generator τ hτ j x hx)
      (Q.map ((rationalEquivalence τ hτ j x hx).toRingHom.comp
        (FractionFiniteCoefficientLift318.toField PolynomialBase RationalBase d hd)))=0:=by
  rw [←Polynomial.map_map,hQ,original_equation]
  exact equation_root τ hτ j x hx

/-- Every specialization at a genuine complex point of the produced
base open retains degree and has no repeated roots. This includes base
points not yet known to lie under the original analytic image. -/
theorem every_specialization {d:PolynomialBase}{Q A B:Polynomial (Localization.Away d)}
    (hm:Q.Monic)(hAB:A*Q+B*Q.derivative=1)
    (hdeg:Q.natDegree=Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j))
    (v:Localization.Away d→+*ℂ):
    (Q.map v).Monic ∧ (Q.map v).Separable ∧
      (Q.map v).natDegree=Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j) ∧
      ∀z:ℂ,Polynomial.aeval z (Q.map v)=0→
        Polynomial.aeval z (Q.map v).derivative≠0:=by
  obtain ⟨hm',hs',hn⟩:=FractionSeparablePolynomialOpen318.specialize (R:=PolynomialBase) hm hAB v
  exact ⟨hm',hs',hn.trans hdeg,fun z hz=>hs'.aeval_derivative_ne_zero hz⟩
end PELOriginalPrimitiveSeparableOpen318
