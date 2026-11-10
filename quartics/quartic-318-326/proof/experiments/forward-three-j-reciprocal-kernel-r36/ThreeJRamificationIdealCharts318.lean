module
public import ThreeJCuspDifferentialCharts318
public section
noncomputable section
namespace ThreeJRamificationIdealCharts318
open Polynomial ThreeJCuspDifferentialCharts318 ThreeProjectiveJCertificates318
open LocalizedRationalDifferentials318
set_option maxHeartbeats 1500000

@[expose] def finiteEquation : ℚ[X] := X^2*(X+243)^2*finiteD
@[expose] def infinityEquation : ℚ[X] := (1+243*X)^2*reciprocalD
lemma finiteEquation_monic : finiteEquation.Monic := by unfold finiteEquation finiteD; monicity!
lemma finiteEquation_degree : finiteEquation.natDegree=6 := by unfold finiteEquation finiteD; compute_degree!
lemma infinityEquation_zero : infinityEquation.eval 0=1 := by norm_num [infinityEquation,reciprocalD]

/-- The finite-cusp chart presentation agrees with the full homogeneous
ramification equation as an ideal, not only as a reduced zero locus. -/
theorem finite_jacobian_ideal : Ideal.span {finiteJacobian}=
    Ideal.map (value finiteNumerator).toRingHom (Ideal.span {finiteEquation}) := by
  have hi : IsUnit finiteInverse := IsUnit.of_mul_eq_one_right _ finite_inverse
  have he : finiteJacobian=value finiteNumerator finiteEquation*(-finiteInverse^2) := by
    simp only [finiteJacobian,finiteCofactor,finiteEquation,map_mul,map_pow,map_add,map_ofNat]
    ring
  rw [he,Ideal.span_singleton_mul_right_unit (hi.pow 2).neg,
    Ideal.map_span,Set.image_singleton]
  rfl

theorem infinity_jacobian_ideal : Ideal.span {infinityJacobian}=
    Ideal.map (value reciprocalNumerator).toRingHom (Ideal.span {infinityEquation}) := by
  have hi : IsUnit infinityInverse := IsUnit.of_mul_eq_one_right _ infinity_inverse
  have he : infinityJacobian=value reciprocalNumerator infinityEquation*infinityInverse^2 := by
    simp only [infinityJacobian,infinityEquation,map_mul,map_pow,map_add,map_one,map_ofNat]
  rw [he,Ideal.span_singleton_mul_right_unit (hi.pow 2),Ideal.map_span,Set.image_singleton]
  rfl

@[expose] def homogeneous {R : Type*} [CommRing R] (x y : R) : R :=
  x^2*(x+243*y)^2*(x^2-486*x*y-19683*y^2)
lemma homogeneous_scale {R : Type*} [CommRing R] (a x y : R) :
    homogeneous (a*x) (a*y)=a^6*homogeneous x y := by unfold homogeneous; ring

/-- The exact degree-six transition, evaluated in the actual original
Laurent intersection. Its scalar is a unit on the entire intersection. -/
theorem overlap_equation :
    Polynomial.aeval (R:=ℚ) ProjectiveLineOverlap318.t finiteEquation=
      ProjectiveLineOverlap318.t^6*
        Polynomial.aeval (R:=ℚ) ProjectiveLineOverlap318.s infinityEquation := by
  have h := homogeneous_scale ProjectiveLineOverlap318.t (1:ProjectiveLineOverlap318.A)
    ProjectiveLineOverlap318.s
  rw [mul_one,ProjectiveLineOverlap318.ts] at h
  simpa only [finiteEquation,infinityEquation,finiteD,reciprocalD,homogeneous,
    map_mul,map_pow,map_add,map_sub,map_one,map_ofNat,Polynomial.aeval_X,
    one_pow,mul_one,one_mul] using h

/-- Actual ideal descent on the full categorical overlap of the original
two projective charts, with every multiplicity retained. -/
theorem overlap_ideal :
    Ideal.map (algebraMap ℚ[X] ProjectiveLineOverlap318.A) (Ideal.span {finiteEquation})=
      Ideal.map (Polynomial.aeval (R:=ℚ) ProjectiveLineOverlap318.s).toRingHom
        (Ideal.span {infinityEquation}) := by
  rw [←ThreeProjectiveJMap318.evaluation_t,Ideal.map_span,Ideal.map_span,
    Set.image_singleton,Set.image_singleton]
  change Ideal.span {Polynomial.aeval (R:=ℚ) ProjectiveLineOverlap318.t finiteEquation}=_
  rw [overlap_equation]
  exact Ideal.span_singleton_mul_left_unit
    ((IsUnit.of_mul_eq_one ProjectiveLineOverlap318.s ProjectiveLineOverlap318.ts).pow 6) _

end ThreeJRamificationIdealCharts318
