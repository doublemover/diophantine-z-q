module
public import PELOriginalCubicRelationIdeal318
public import PELOriginalAllLevelProjectiveMap318
public import HomogeneousEvaluationScaling318
public section
noncomputable section
namespace PELOriginalHomogeneousRelationVanishing318
open PELOriginalCubicRelationIdeal318 PELOriginalSectionMultiplication318
open PELOriginalAllLevelProjectiveMap318 PELOriginalPolarizationTransitions318
variable (τ:ℂ)(hτ:0<τ.im)
@[expose] def pointEvaluation(q:Base τ):Values τ→+*ℂ where
  toFun f:=f q
  map_one':=rfl
  map_zero':=rfl
  map_add' _ _:=rfl
  map_mul' _ _:=rfl
lemma evaluate_at_point(p:Equations)(q:Base τ):
    (MvPolynomial.eval₂Hom (algebraMap ℂ (Values τ)) (vector τ hτ) p) q=
      MvPolynomial.eval (baseVector τ hτ 1 q) p:=by
  have h:=MvPolynomial.map_eval₂Hom (algebraMap ℂ (Values τ)) (vector τ hτ)
    (pointEvaluation τ q) p
  exact h

/-- A homogeneous relation is equivalent to vanishing at EVERY actual
original source point, evaluated on the SAME nine selected-gauge cubic
sections defining its projective map. The converse uses true section
values, not an assumed algebraic image theorem. -/
theorem homogeneous_relation_iff(p:Equations)(n:ℕ)(hp:p.IsHomogeneous n):
    p∈relations τ hτ↔∀q:Base τ,MvPolynomial.eval (baseVector τ hτ 1 q) p=0:=by
  rw [relation_iff,underlying_presentation,
    CubicHomogeneousMarker318.homogeneous_marker _ _ p n hp]
  constructor
  · intro h q
    have hc:=congrArg (fun f:Polynomial (Values τ)=>f.coeff (3*n)) h
    simp only [Polynomial.coeff_monomial_same,Polynomial.coeff_zero] at hc
    have hq:=congrFun hc q
    rwa [evaluate_at_point] at hq
  · intro h
    have hz:MvPolynomial.eval₂Hom (algebraMap ℂ (Values τ)) (vector τ hτ) p=0:=by
      funext q
      exact (evaluate_at_point τ hτ p q).trans (h q)
    rw [hz,Polynomial.monomial_zero_right]

/-- This is a homogeneous relation locus, defined degreewise from the
actual kernel. Mixed-degree evaluations are NOT used to define projective
vanishing. No equality with the analytic image is asserted. -/
@[expose] def zeroCone:Set (Coordinates 1):=
  {v|∀p:Equations,∀n:ℕ,p.IsHomogeneous n→p∈relations τ hτ→MvPolynomial.eval v p=0}
theorem original_vectors_in_zeroCone(q:Base τ):baseVector τ hτ 1 q∈zeroCone τ hτ:=by
  intro p n hp hr
  exact (homogeneous_relation_iff τ hτ p n hp).mp hr q
lemma zeroCone_scale(v:Coordinates 1)(hv:v∈zeroCone τ hτ)(a:ℂ):
    (a • v)∈zeroCone τ hτ:=by
  intro p n hp hr
  change MvPolynomial.eval (fun i=>a*v i) p=0
  rw [HomogeneousEvaluationScaling318.evaluate_scale p n hp, hv p n hp hr,mul_zero]
/-- The intrinsic projective relation locus tests EVERY representative;
its definition is independent of any chosen bundle gauge. -/
@[expose] def projectiveZeroLocus:Set (Projectivization ℂ (Coordinates 1)):=
  {p|∀v:Coordinates 1,∀hv:v≠0,Projectivization.mk ℂ v hv=p→v∈zeroCone τ hτ}
theorem original_image_in_projective_zero_locus:
    Set.range (projectiveMap τ hτ 1)⊆projectiveZeroLocus τ hτ:=by
  rintro p ⟨q,rfl⟩ v hv he
  obtain ⟨a,ha⟩:=(Projectivization.mk_eq_mk_iff' ℂ v (baseVector τ hτ 1 q)
    hv (baseVector_nonzero τ hτ 1 q)).mp he
  rw [←ha]
  exact zeroCone_scale τ hτ _ (original_vectors_in_zeroCone τ hτ q) a
end PELOriginalHomogeneousRelationVanishing318
