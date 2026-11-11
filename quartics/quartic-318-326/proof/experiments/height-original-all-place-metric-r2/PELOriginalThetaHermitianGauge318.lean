module
public import PELOriginalThetaQuasiperiods318
public import PELOriginalPolarizationAutomorphy318
public section
noncomputable section
namespace PELOriginalThetaHermitianGauge318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalThetaQuasiperiods318
open PELOriginalSiegelNormalization318 PELOriginalSymplecticCoordinates318
variable (τ:ℂ) (hτ:0<τ.im)
variable (B:ComplexVectors→ₗ[ℂ]ComplexVectors→ₗ[ℂ]ℂ)
  (hB:∀z w,B z w=B w z)
  (hperiod:∀(p:Pair) (z:ComplexVectors),
    B z (standardPeriod τ p)-normalizedHermitian τ hτ z (standardPeriod τ p)=
      2*Complex.I*linear (p.2 0,p.2 1) z)

@[expose] def gauge (z:ComplexVectors):ℂ:=Complex.exp ((Real.pi:ℂ)/2*B z z)
lemma gauge_nonzero (z:ComplexVectors):gauge B z≠0:=Complex.exp_ne_zero _
lemma diagonal_add (z w:ComplexVectors):B (z+w) (z+w)=B z z+2*B z w+B w w:=by
  simp only [map_add,LinearMap.add_apply]
  rw [hB w z]
  ring
lemma linear_period (p:Pair):
    linear (p.2 0,p.2 1) (standardPeriod τ p)=
      (canonicalQuadratic p:ℂ)+quadratic τ (p.2 0,p.2 1):=by
  simp only [linear,standardPeriod,canonicalQuadratic,quadratic]
  push_cast
  ring

/-- The explicit quadratic gauge converts the actual classical theta
multiplier to the SAME original normalized Appell-Humbert factor, including
its exact characteristic. The matrix identity is isolated for the actual
producer to instantiate, rather than asserting equality from j-invariants. -/
theorem exact_multiplier (p:Pair) (z:ComplexVectors):
    gauge B (z+standardPeriod τ p)*multiplier τ (p.2 0,p.2 1) z=
      normalizedFactor τ hτ p z*gauge B z:=by
  rw [normalized_factor_formula τ hτ p z]
  simp only [gauge,multiplier,←Complex.exp_add]
  congr 1
  rw [diagonal_add B hB]
  have h0:=hperiod p z
  have h1:=hperiod p (standardPeriod τ p)
  rw [linear_period] at h1
  linear_combination (Real.pi:ℂ)*h0+(Real.pi:ℂ)/2*h1

@[expose] def gaugedTheta (z:ComplexVectors):ℂ:=gauge B z*theta τ z
lemma original_factor (p:Pair) (z:ComplexVectors):
    gaugedTheta τ B (z+standardPeriod τ p)=
      normalizedFactor τ hτ p z*gaugedTheta τ B z:=by
  rw [gaugedTheta,theta_original_period]
  rw [←mul_assoc,exact_multiplier τ hτ B hB hperiod]
  rfl
end PELOriginalThetaHermitianGauge318
