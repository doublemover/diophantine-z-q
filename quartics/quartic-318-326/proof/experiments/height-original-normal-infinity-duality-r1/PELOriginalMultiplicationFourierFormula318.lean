module
public import PELOriginalThetaMultiplicationConstants318
public section
noncomputable section
namespace PELOriginalMultiplicationFourierFormula318
open QuaternionicRealPeriod318 PELOriginalSectionMultiplication318
open PELOriginalWholeHZeroDimension318 PELOriginalWholeSectionSpanning318
open PELOriginalPowerSectionLift318 PELOriginalPowerSectionDescent318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalThetaMultiplicationConstants318 PELOriginalSectionGaugeNormalization318
open PELOriginalThetaHermitianGauge318 PELOriginalThetaGaugeMatrix318 PELOriginalSiegelNormalization318
variable (τ:ℂ)(hτ:0<τ.im)
lemma actual_coefficients(k:ℕ)[NeZero k](s:HZero τ hτ k):
    (coefficientEquivalence τ hτ k).symm s=
      PELOriginalWholeSectionSpanning318.coordinates τ hτ k (asSection τ hτ k s):=by
  apply (coefficientEquivalence τ hτ k).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext q
  change s.val q=(expansionMap τ hτ k
    (PELOriginalWholeSectionSpanning318.coordinates τ hτ k (asSection τ hτ k s))).val q
  rw [expansionMap_value]
  exact whole_section_spanning τ hτ k (asSection τ hτ k s) q
lemma theta_lift(k:ℕ)[NeZero k](r:Label k)(z:ComplexVectors):
    lift τ hτ k (asSection τ hτ k (thetaVector τ hτ k r)) z=value τ hτ k r z:=by
  let f:OriginalAutomorphic τ hτ k:=
    ⟨value τ hτ k r,PELOriginalLevelPowerSections318.holomorphic τ hτ k r,
      PELOriginalLevelPowerSections318.original_automorphy τ hτ k r⟩
  have he:asSection τ hτ k (thetaVector τ hτ k r)=descend τ hτ k f:=rfl
  rw [he,lift_descend]
  rfl

variable (m n:ℕ)[NeZero m][NeZero n]
local instance sum_ne_zero:NeZero (m+n):=⟨Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero (NeZero.ne m)) n)⟩
/-- Actual original tensor multiplication loses NO character or scalar
when its common original quadratic gauge is removed: precisely the
product of the two independently convergent characteristic thetas remains. -/
lemma normalized_product(r:Label m)(s:Label n):
    normalize τ hτ (m+n) (ascend τ hτ (m+n)
      (asSection τ hτ (m+n) (multiply τ hτ m n (thetaVector τ hτ m r) (thetaVector τ hτ n s))))=
      fun z:ComplexVectors=>levelTheta τ m r z*levelTheta τ n s z:=by
  funext z
  change lift τ hτ (m+n)
    (asSection τ hτ (m+n) (multiply τ hτ m n (thetaVector τ hτ m r) (thetaVector τ hτ n s)))
      ((normalization τ hτ).symm z)/gauge (bilinearMap τ) z^(m+n)=_
  rw [lift_product,theta_lift,theta_lift]
  simp only [value,normalizedValue,LinearEquiv.apply_symm_apply,pow_add]
  field_simp [pow_ne_zero m (gauge_nonzero (bilinearMap τ) z),
    pow_ne_zero n (gauge_nonzero (bilinearMap τ) z)]

/-- Exact computable Fourier-integral formula for every original theta
multiplication constant. The normalized coefficient is divided by the
proved nonzero leading Fourier coefficient of the genuine target basis;
this is not merely existence of an unspecified multiplication table. -/
theorem structure_constant_fourier(r:Label m)(s:Label n)(t:Label (m+n)):
    structureConstant τ hτ m n r s t=
      EntireDoubleFourierTranslation318.coefficient
        (fun z:ComplexVectors=>levelTheta τ m r z*levelTheta τ n s z)
        (PELOriginalLevelThetaIndependence318.representative (m+n) t)/
      PELOriginalLevelThetaIndependence318.leading τ (m+n) t:=by
  change ((coefficientEquivalence τ hτ (m+n)).symm
    (multiply τ hτ m n (coefficientEquivalence τ hτ m (Pi.single r 1))
      (coefficientEquivalence τ hτ n (Pi.single s 1)))) t=_
  rw [coefficient_basis,coefficient_basis,actual_coefficients]
  change PELOriginalAutomorphicSpanning318.coordinates τ (m+n)
    (normalize τ hτ (m+n) (ascend τ hτ (m+n)
      (asSection τ hτ (m+n) (multiply τ hτ m n (thetaVector τ hτ m r) (thetaVector τ hτ n s))))) t=_
  rw [normalized_product]
  rfl
end PELOriginalMultiplicationFourierFormula318
