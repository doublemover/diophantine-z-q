module
public import PELOriginalPrimitiveRegularOpen318
public section
noncomputable section
namespace PELOriginalPrimitiveGeneratorExpressions318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
open PELOriginalProjectedPrimitivePolynomial318 PELOriginalPrimitiveSeparableOpen318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)(x:ComplexVectors)(hx:value τ hτ 3 j x≠0)
local instance chartDomain:IsDomain (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
local instance chartFiniteType:Algebra.FiniteType ℂ (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartFiniteType318.finite_type τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
/-- A genuine finite generating set of the ENTIRE original chart has
bounded primitive polynomial expressions whose COMPLETE coefficient
families are regular on ONE produced nonzero polynomial base open.
The same primitive generator and every original chart generator remain
visible; no monogenic-order equality is assumed in this producer. -/
theorem exists_generator_expressions:
    ∃s:Finset (CoordinateChart τ hτ j),
      Algebra.adjoin ℂ (s:Set (CoordinateChart τ hτ j))=⊤ ∧
      ∃d:PolynomialBase,∃hd:d≠0,∃P:s→Polynomial (Localization.Away d),
        ∀a:s,
          Polynomial.aeval (generator τ hτ j x hx)
            ((P a).map ((rationalEquivalence τ hτ j x hx).toRingHom.comp
              (FractionFiniteCoefficientLift318.toField PolynomialBase RationalBase d hd)))=
            algebraMap (CoordinateChart τ hτ j) (OriginalField τ hτ j) a ∧
          (P a).natDegree<(equation τ hτ j x hx).natDegree:=by
  classical
  obtain ⟨s,hs⟩:=Algebra.FiniteType.out (R:=ℂ) (A:=CoordinateChart τ hτ j)
  choose p hp he using fun a:s=>original_coordinate_expression τ hτ j x hx a
  let e:=rationalEquivalence τ hτ j x hx
  let f(a:s):Polynomial RationalBase:=(p a).map e.symm.toRingHom
  obtain ⟨d,hd,P,hP⟩:=FractionPolynomialFamilyLift318.exists_lift PolynomialBase RationalBase f
  let v:=e.toRingHom.comp (FractionFiniteCoefficientLift318.toField PolynomialBase RationalBase d hd)
  have hv:Function.Injective v:=e.injective.comp
    (FractionFiniteCoefficientLift318.toField_injective PolynomialBase RationalBase d hd)
  have hmap(a:s):(P a).map v=p a:=by
    rw [v,←Polynomial.map_map,hP]
    ext n
    simp only [f,Polynomial.coeff_map]
    exact e.apply_symm_apply _
  refine ⟨s,hs,d,hd,P,?_⟩
  intro a
  refine ⟨?_,?_⟩
  · change Polynomial.aeval (generator τ hτ j x hx) ((P a).map v)=_
    rw [hmap]
    exact (he a).symm
  · have hn:=Polynomial.natDegree_map_eq_of_injective hv (P a)
    rw [hmap] at hn
    rw [←hn]
    exact hp a
end PELOriginalPrimitiveGeneratorExpressions318
