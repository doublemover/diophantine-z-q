module
public import QuadraticMonomialCoordinates318
public import PELOriginalRelationSaturation318
public import PELOriginalThetaMultiplicationConstants318
public section
noncomputable section
namespace PELOriginalQuadraticMultiplication318
open PELOriginalLevelTheta318 PELOriginalWholeHZeroDimension318
open PELOriginalCubicRelationIdeal318 PELOriginalSectionMultiplication318
open PELOriginalGradedSectionRing318 PELOriginalThetaMultiplicationConstants318
open QuadraticMonomialCoordinates318
variable (τ:ℂ)(hτ:0<τ.im)
abbrev Quad:=Index (Label 3)
abbrev Coefficients:=Quad→ℂ
@[expose] def product(a:Quad):HZero τ hτ 6:=
  multiply τ hτ 3 3 (thetaVector τ hτ 3 (first (Label 3) a))
    (thetaVector τ hτ 3 (second (Label 3) a))
@[expose] def sectionMap:Coefficients→ₗ[ℂ]HZero τ hτ 6 where
  toFun c:=∑a:Quad,c a • product τ hτ a
  map_add' c d:=by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c d:=by simp only [Pi.smul_apply,mul_smul,Finset.smul_sum,RingHom.id_apply]
/-- Genuine multiplication into the FULL original degree6 section
space. There are 45 unordered input monomials and 36 actual output
coordinates; surjectivity is NOT an input or a conclusion here. -/
@[expose] def matrixMap:Coefficients→ₗ[ℂ](Label 6→ℂ):=
  (coefficientEquivalence τ hτ 6).symm.toLinearMap.comp (sectionMap τ hτ)
@[expose] def matrix:Matrix (Label 6) Quad ℂ:=fun t a=>
  (coefficientEquivalence τ hτ 6).symm (product τ hτ a) t
lemma matrix_entry(a:Quad)(t:Label 6):matrix τ hτ t a=
    structureConstant τ hτ 3 3 (first (Label 3) a) (second (Label 3) a) t:=by
  change ((coefficientEquivalence τ hτ 6).symm
    (multiply τ hτ 3 3 (thetaVector τ hτ 3 _) (thetaVector τ hτ 3 _))) t=_
  simp only [structureConstant,coordinateProduct,LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,coefficient_basis]
lemma matrixMap_apply(c:Coefficients)(t:Label 6):
    matrixMap τ hτ c t=∑a:Quad,matrix τ hτ t a*c a:=by
  simp only [matrixMap,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,sectionMap,
    LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_comm _ _
lemma sectionMap_single(a:Quad):sectionMap τ hτ (Pi.single a 1)=product τ hτ a:=by
  simp [sectionMap]
lemma monomial_image(a:Quad):
    presentation τ hτ (MvPolynomial.monomial (exponent (Label 3) a) 1)=
      includeDegree τ hτ 6 (product τ hτ a):=by
  rw [monomial_actual_pair,map_mul,variable_image,variable_image]
  exact homogeneous_product τ hτ 3 3 _ _
lemma polynomial_sum(c:Coefficients):
    polynomial (Label 3) c=∑a:Quad,c a • MvPolynomial.monomial (exponent (Label 3) a) 1:=by
  change (∑a:Quad,MvPolynomial.monomial (exponent (Label 3) a) (c a))=_
  apply Finset.sum_congr rfl
  intro a ha
  rw [←map_smul,smul_eq_mul,mul_one]
/-- Actual polynomial evaluation agrees with the independently
constructed section product, degree by degree in the SAME section ring. -/
theorem presentation_polynomial(c:Coefficients):
    presentation τ hτ (polynomial (Label 3) c)=
      includeDegree τ hτ 6 (sectionMap τ hτ c):=by
  rw [polynomial_sum,map_sum]
  simp only [map_smul,monomial_image,sectionMap,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,map_smul]
/-- A vector is in this genuine 45-to-36 multiplication kernel exactly
when its nonredundant quadratic polynomial is an ACTUAL original
relation. Antisymmetric ordered-pair artifacts cannot enter. -/
theorem kernel_iff_relation(c:Coefficients):
    matrixMap τ hτ c=0↔polynomial (Label 3) c∈relations τ hτ:=by
  change matrixMap τ hτ c=0↔presentation τ hτ (polynomial (Label 3) c)=0
  rw [presentation_polynomial]
  have hi:=include_injective τ hτ 6
  have he:matrixMap τ hτ c=0↔sectionMap τ hτ c=0:=by
    change (coefficientEquivalence τ hτ 6).symm (sectionMap τ hτ c)=0↔_
    constructor
    · intro hc
      apply (coefficientEquivalence τ hτ 6).symm.injective
      simpa only [map_zero] using hc
    · intro hc
      rw [hc,map_zero]
  rw [he]
  constructor
  · intro hc
    rw [hc,map_zero]
  · intro hc
    apply hi
    simpa only [map_zero] using hc
end PELOriginalQuadraticMultiplication318
