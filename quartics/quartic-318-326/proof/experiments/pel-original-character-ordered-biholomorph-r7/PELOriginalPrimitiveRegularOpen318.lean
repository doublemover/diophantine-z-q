module
public import PELOriginalPrimitiveSeparableOpen318
public import AlgebraicFractionBaseDenominator318
public section
noncomputable section
namespace PELOriginalPrimitiveRegularOpen318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedPrimitivePolynomial318
open PELOriginalPrimitiveSeparableOpen318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)(x:ComplexVectors)(hx:value τ hτ 3 j x≠0)
local instance chartDomain:IsDomain (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
/-- The SAME primitive field generator becomes an actual REGULAR
function on the whole preimage of a produced nonzero polynomial base
open. The denominator is in the two original projected coordinates,
not an arbitrary source function whose vanishing could discard fibers. -/
theorem exists_regular_primitive:
    ∃p:PolynomialBase,∃hp:p≠0,
      ∃ha:MvPolynomial.aeval (projectedFunction τ hτ x j) p≠0,
        ∃β:Localization.Away (MvPolynomial.aeval (projectedFunction τ hτ x j) p),
          FractionFiniteCoefficientLift318.toField (CoordinateChart τ hτ j)
            (OriginalField τ hτ j) (MvPolynomial.aeval (projectedFunction τ hτ x j) p) ha β=
              generator τ hτ j x hx:=by
  let A:=CoordinateChart τ hτ j
  let R:=projectedBase τ hτ j x
  let K:=OriginalField τ hτ j
  let pair:=projectedFunction τ hτ x j
  have hi:AlgebraicIndependent ℂ pair:=independent τ hτ x j hx
  letI : Algebra.IsAlgebraic R A:=
    IndependentPairGenericFinite318.algebraic_over_pair A pair hi
      (PELOriginalAffineChartTranscendence318.actual_chart_trdeg_le_two τ hτ j)
  obtain ⟨d,hd,c,hc⟩:=AlgebraicFractionBaseDenominator318.exists_base_multiple R A K
    (generator τ hτ j x hx)
  let p:PolynomialBase:=hi.aevalEquiv.symm d
  have hp:p≠0:=by
    intro hz
    apply hd
    have he:=congrArg hi.aevalEquiv hz
    simpa only [p,AlgEquiv.apply_symm_apply,map_zero] using he
  have he:algebraMap R A d=MvPolynomial.aeval pair p:=by
    rw [←hi.algebraMap_aevalEquiv p]
    exact congrArg (algebraMap R A) (hi.aevalEquiv.apply_symm_apply d).symm
  have hr:Function.Injective (algebraMap R A):=Subtype.val_injective
  have ha:MvPolynomial.aeval pair p≠0:=by
    rw [←he]
    simpa only [map_zero] using hr.ne hd
  let y:Submonoid.powers (MvPolynomial.aeval pair p):=⟨_,⟨1,pow_one _⟩⟩
  refine ⟨p,hp,ha,IsLocalization.mk' (Localization.Away (MvPolynomial.aeval pair p)) c y,?_⟩
  apply (IsLocalization.lift_mk'_spec
    (FractionFiniteCoefficientLift318.powers_units A K _ ha) _ _ _).mpr
  change algebraMap A K c=algebraMap A K (MvPolynomial.aeval pair p)*generator τ hτ j x hx
  rw [←he,←IsScalarTower.algebraMap_apply R A K]
  exact hc.symm
end PELOriginalPrimitiveRegularOpen318
