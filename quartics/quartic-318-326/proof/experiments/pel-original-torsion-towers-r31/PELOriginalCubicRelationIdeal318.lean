module
public import PELOriginalSectionDegreeZero318
public import CubicHomogeneousMarker318
public section
noncomputable section
namespace PELOriginalCubicRelationIdeal318
open PELOriginalSectionMultiplication318 PELOriginalGradedSectionRing318
open PELOriginalWholeHZeroDimension318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
variable (τ:ℂ)(hτ:0<τ.im)
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev Equations:=MvPolynomial (Label 3) ℂ
/-- The nine ACTUAL cubic sections, in the true original graded ring. -/
@[expose] def generators(r:Label 3):Ring τ hτ:=
  includeDegree τ hτ 3 (thetaVector τ hτ 3 r)
@[expose] def presentation:Equations→ₐ[ℂ]Ring τ hτ:=MvPolynomial.aeval (generators τ hτ)
/-- Actual section relations, not an ideal chosen to fit an anticipated
algebraic model or the numerical PEL branch parameters. -/
@[expose] def relations:Ideal Equations:=RingHom.ker (presentation τ hτ).toRingHom
@[expose] def vector:Label 3→Values τ:=fun r=>(thetaVector τ hτ 3 r).val
lemma underlying_presentation(p:Equations):
    (presentation τ hτ p).val=
      CubicHomogeneousMarker318.marker (algebraMap ℂ (Values τ)) (vector τ hτ) p:=by
  have he:(sectionAlgebra τ hτ).val.comp (presentation τ hτ)=
      MvPolynomial.aeval (fun r:Label 3=>Polynomial.monomial 3 (vector τ hτ r)):=by
    apply MvPolynomial.algHom_ext
    intro r
    simp only [AlgHom.comp_apply,presentation,MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun f:Equations→ₐ[ℂ]Polynomial (Values τ)=>f p) he
lemma relation_iff(p:Equations):p∈relations τ hτ↔(presentation τ hτ p).val=0:=by
  change presentation τ hτ p=0↔_
  constructor
  · intro h;exact congrArg Subtype.val h
  · intro h;exact Subtype.ext h

/-- Every homogeneous component of an actual relation is an actual
relation. This is DERIVED from distinct formal degrees 3n of the same
section algebra, not assumed from pointwise vanishing. -/
theorem homogeneous_component_mem(p:Equations)(hp:p∈relations τ hτ)(n:ℕ):
    MvPolynomial.homogeneousComponent n p∈relations τ hτ:=by
  rw [relation_iff,underlying_presentation,
    CubicHomogeneousMarker318.homogeneous_component]
  have hz:= (relation_iff τ hτ p).mp hp
  rw [underlying_presentation] at hz
  rw [hz,Polynomial.coeff_zero,Polynomial.monomial_zero_right]

/-- Exact all-component characterization of the homogeneous relation
ideal. No Proj/analytic-image identification or normal generation follows
merely from this algebraic presentation. -/
theorem relation_iff_components(p:Equations):
    p∈relations τ hτ↔∀n,MvPolynomial.homogeneousComponent n p∈relations τ hτ:=by
  constructor
  · exact fun hp n=>homogeneous_component_mem τ hτ p hp n
  · intro hp
    rw [←MvPolynomial.sum_homogeneousComponent p]
    exact (relations τ hτ).sum_mem (fun n hn=>hp n)
theorem relations_homogeneous:
    (relations τ hτ).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Label 3) ℂ):=by
  intro n p hp
  change ((MvPolynomial.decomposition.decompose' p n):Equations)∈relations τ hτ
  rw [MvPolynomial.decomposition.decompose'_apply]
  exact homogeneous_component_mem τ hτ p hp n
lemma variable_image(r:Label 3):presentation τ hτ (MvPolynomial.X r)=generators τ hτ r:=
  MvPolynomial.aeval_X _ _
end PELOriginalCubicRelationIdeal318
