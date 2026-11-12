module
public import PELOriginalProjectedGenericFinite318
public import Mathlib.FieldTheory.PrimitiveElement
public section
noncomputable section
namespace PELOriginalProjectedPrimitivePolynomial318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)(x:ComplexVectors)(hx:value τ hτ 3 j x≠0)
local instance chartDomain:IsDomain (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
abbrev BaseField:=projectedRationalBase τ hτ j x
abbrev OriginalField:=actualChartFunctionField τ hτ j
local instance finiteField:Module.Finite (BaseField τ hτ j x) (OriginalField τ hτ j):=
  actual_finite_generic_degree τ hτ j x hx

/-- A genuine primitive power basis in the SAME actual chart field over
its specified original projected-coordinate field. Characteristic zero
and the produced finite extension supply separability internally. -/
@[expose] def powerBasis:PowerBasis (BaseField τ hτ j x) (OriginalField τ hτ j):=
  Field.powerBasisOfFiniteOfSeparable (BaseField τ hτ j x) (OriginalField τ hτ j)
@[expose] def generator:OriginalField τ hτ j:=(powerBasis τ hτ j x hx).gen
@[expose] def equation:Polynomial (BaseField τ hτ j x):=
  minpoly (BaseField τ hτ j x) (generator τ hτ j x hx)
lemma equation_monic:(equation τ hτ j x hx).Monic:=
  minpoly.monic (powerBasis τ hτ j x hx).isIntegral_gen
lemma equation_irreducible:Irreducible (equation τ hτ j x hx):=
  minpoly.irreducible (powerBasis τ hτ j x hx).isIntegral_gen
lemma equation_separable:(equation τ hτ j x hx).Separable:=
  (equation_irreducible τ hτ j x hx).separable
lemma equation_root:Polynomial.aeval (generator τ hτ j x hx) (equation τ hτ j x hx)=0:=
  minpoly.aeval _ _
lemma actual_degree:(equation τ hτ j x hx).natDegree=
    Module.finrank (BaseField τ hτ j x) (OriginalField τ hτ j):=
  (powerBasis τ hτ j x hx).natDegree_minpoly.trans (powerBasis τ hτ j x hx).finrank.symm
lemma positive_degree:0<(equation τ hτ j x hx).natDegree:=by
  change 0<(minpoly (BaseField τ hτ j x) (powerBasis τ hτ j x hx).gen).natDegree
  rw [(powerBasis τ hτ j x hx).natDegree_minpoly]
  exact (powerBasis τ hτ j x hx).dim_pos

/-- Actual polynomial Bezout data, before any specialization. Clearing
its finitely many coefficients will preserve the no-multiple-root
certificate on a produced base open; that step is not assumed here. -/
theorem derivative_bezout:
    ∃a b:Polynomial (BaseField τ hτ j x),
      a*equation τ hτ j x hx+b*(equation τ hτ j x hx).derivative=1:=
  (Polynomial.separable_def' _).mp (equation_separable τ hτ j x hx)
lemma derivative_at_generator_ne_zero:
    Polynomial.aeval (generator τ hτ j x hx) (equation τ hτ j x hx).derivative≠0:=
  (equation_separable τ hτ j x hx).aeval_derivative_ne_zero (equation_root τ hτ j x hx)

/-- EVERY original chart function is a polynomial of bounded degree in
this actual primitive generator, over the SAME original rational base.
This is full coordinate recovery, not just a primitive-field existence
with unspecified relation to the original chart. -/
theorem original_coordinate_expression(a:CoordinateChart τ hτ j):
    ∃p:Polynomial (BaseField τ hτ j x),
      p.natDegree<(equation τ hτ j x hx).natDegree∧
        algebraMap (CoordinateChart τ hτ j) (OriginalField τ hτ j) a=
          Polynomial.aeval (generator τ hτ j x hx) p:=by
  obtain ⟨p,hp,he⟩:=(powerBasis τ hτ j x hx).exists_eq_aeval
    (algebraMap (CoordinateChart τ hτ j) (OriginalField τ hτ j) a)
  refine ⟨p,?_,he⟩
  simpa only [equation,generator,(powerBasis τ hτ j x hx).natDegree_minpoly] using hp
end PELOriginalProjectedPrimitivePolynomial318
