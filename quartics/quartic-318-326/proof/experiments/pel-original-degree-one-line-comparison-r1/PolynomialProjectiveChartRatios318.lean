module
public import HomogeneousQuotientChartSupport318
public import ComplexProjectiveBase318
public section
noncomputable section
namespace PolynomialProjectiveChartRatios318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
open HomogeneousQuotientChart318 HomogeneousQuotientChartSupport318
variable {ι : Type*} (j : ι)
local instance standardGrading : GradedAlgebra (grading (ι := ι)) := MvPolynomial.gradedAlgebra

/-- The literal constant inclusion in the actual degree-zero chart. -/
@[expose] def scalar : ℂ →+* Chart j :=
  (HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers (MvPolynomial.X j))).comp
    ComplexProjectiveBase318.constants.toRingHom
lemma scalar_fraction (c : ℂ) : scalar j c =
    fraction j 0 (MvPolynomial.C c) (MvPolynomial.isHomogeneous_C ι c) := rfl

@[expose] def ratio (i : ι) : Chart j :=
  fraction j 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i)

lemma ratio_self : ratio j j = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [ratio,fraction,HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one,pow_one]
  exact Localization.mk_self _

/-- Exact homogeneous linear relation in the full standard chart ring. -/
lemma linear_fraction (i : ι) (c : ℂ) :
    fraction j 1 (MvPolynomial.X i-MvPolynomial.C c*MvPolynomial.X j)
      ((MvPolynomial.isHomogeneous_X ℂ i).sub
        ((MvPolynomial.isHomogeneous_C ι c).mul (MvPolynomial.isHomogeneous_X ℂ j))) =
      ratio j i-scalar j c := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_sub,ratio,scalar_fraction,fraction,
    HomogeneousLocalization.Away.val_mk,pow_one,pow_zero,Localization.sub_mk,
    OneMemClass.coe_one,Submonoid.coe_mul,one_mul,mul_one]
  congr 1
  ring

@[reassoc] lemma chart_over_complex :
    chartMorphism j ≫ ComplexProjectiveBase318.structureMap =
      Spec.map (CommRingCat.ofHom (scalar j)) := by
  change Proj.awayι _ _ (MvPolynomial.isHomogeneous_X ℂ j) (by norm_num) ≫
    (Proj.toSpecZero _ ≫ ComplexProjectiveBase318.baseIso.hom) = _
  rw [Proj.awayι_toSpecZero_assoc,←Spec.map_comp]
  rfl

/-- Every actual chart evaluation with the original complex scalar
square evaluates the regular ratio to the literal projective ratio.
The proof uses the full homogeneous-prime action and linear relation,
not a presumed formula for analytification of sections. -/
theorem evaluation_ratio (f : Chart j →+* ℂ) (hc : ∀ c, f (scalar j c)=c)
    (v : ι → ℂ) (hv : ∃ i,v i≠0) (hj : v j≠0)
    (hp : chartMorphism j (PrimeSpectrum.comap f (IsLocalRing.closedPoint ℂ)) =
      ComplexProjectiveMarkerPoint318.point v hv) (i : ι) :
    f (ratio j i)=v i/v j := by
  let p : MvPolynomial ι ℂ := MvPolynomial.X i-MvPolynomial.C (f (ratio j i))*MvPolynomial.X j
  have hhom : p.IsHomogeneous 1 :=
    (MvPolynomial.isHomogeneous_X ℂ i).sub
      ((MvPolynomial.isHomogeneous_C ι _).mul (MvPolynomial.isHomogeneous_X ℂ j))
  have he : f (fraction j 1 p hhom)=0 := by
    rw [linear_fraction,map_sub,hc,sub_self]
  have hm : fraction j 1 p hhom ∈
      (PrimeSpectrum.comap f (IsLocalRing.closedPoint ℂ)).asIdeal := by
    change f (fraction j 1 p hhom) ∈ IsLocalRing.maximalIdeal ℂ
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact he
  have hnum := (positive_fraction_mem j _ 1 (by norm_num) p hhom).mp hm
  rw [hp,ComplexProjectiveMarkerPoint318.homogeneous_mem_iff v hv p 1 hhom] at hnum
  change MvPolynomial.eval v p=0 at hnum
  simp only [p,map_sub,map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C] at hnum
  apply (eq_div_iff hj).mpr
  exact (sub_eq_zero.mp hnum).symm
end PolynomialProjectiveChartRatios318
