module
public import InfinityBasisUnitCoefficients318
public import OriginalCharacterClassPullbacks318

public section
noncomputable section
namespace OriginalCharacterSimplePole318
open Polynomial SourceTwistArithmetic318 CubicInverseCoordinates318
open ContactInfinityRegularFractions318 OriginalInfinityCoefficient318
open InfinityBasisUnitCoefficients318 SourceHOneCharacterIndices318
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField : Field (InfinityFieldCoordinates318.L units) :=
  (KummerTensorField318.source_raw_field units).toField

@[expose] def numeratorPolynomial (i : Fin 4) : ℚ[X] :=
  C (xScale i : ℚ)^2 * (C (units 0 : ℚ) - C (centroid i) * X^2)^2

@[expose] def denominatorUnit (i : Fin 4) : (Base units)ˣ :=
  Units.map (algebraMap ℚ (Base units)).toMonoidHom (yScale i * (units 0)^3) *
    (coefficient_unit units (smallIndex (some i)).val.1).unit

@[expose] def numeratorCoefficient (i : Fin 4) : Base units :=
  algebraMap ℚ[X] (Base units) (numeratorPolynomial i) * ↑(denominatorUnit i)⁻¹

/-- A literal element of the original whole infinity order. -/
@[expose] def numerator (i : Fin 4) : InfinityRing units :=
  numeratorCoefficient i • ContactHOneOrderBases318.infinityBasis units (smallIndex (some i)).val.1

/-- The basis-square coefficient is retained in the denominator, not discarded as a scalar. -/
theorem numerator_times_unit (i : Fin 4) :
    numerator i * (CompletedCharacterInfinity318.coefficientUnit i : InfinityRing units) =
      algebraMap (Base units) (InfinityRing units)
        (algebraMap ℚ[X] (Base units) (numeratorPolynomial i)) := by
  let e := ContactHOneOrderBases318.infinityBasis units (smallIndex (some i)).val.1
  let v : Base units := algebraMap ℚ (Base units) (↑(yScale i * (units 0)^3) : ℚ)
  have hu : (CompletedCharacterInfinity318.coefficientUnit i : InfinityRing units) =
      algebraMap (Base units) (InfinityRing units) v * e := by
    change algebraMap ℚ (InfinityRing units) (↑(yScale i * (units 0)^3) : ℚ) *
      ↑(InfinityCharacterUnits318.ratioProduct_unit units i).unit = _
    rw [(InfinityCharacterUnits318.ratioProduct_unit units i).unit_spec,ratioProduct_basis]
    change _ = algebraMap (Base units) (InfinityRing units)
      (algebraMap ℚ (Base units) (↑(yScale i * (units 0)^3) : ℚ)) * _
    rw [RingHom.map_rat_algebraMap]
  have hd : (denominatorUnit i : Base units) = v * squareCoefficient units (smallIndex (some i)).val.1 := by
    change v * ↑(coefficient_unit units (smallIndex (some i)).val.1).unit = _
    rw [(coefficient_unit units (smallIndex (some i)).val.1).unit_spec]
  rw [hu]
  change (numeratorCoefficient i • e) * (algebraMap (Base units) (InfinityRing units) v * e) = _
  rw [NativeTensorScalar318.three_smul (InfinityOrderCoordinates318.coefficient units)]
  change (algebraMap (Base units) (InfinityRing units) (numeratorCoefficient i) * e) *
    (algebraMap (Base units) (InfinityRing units) v * e) = _
  calc
    _ = algebraMap (Base units) (InfinityRing units) (numeratorCoefficient i * v) * e^2 := by
      rw [map_mul]
      ring
    _ = algebraMap (Base units) (InfinityRing units)
        (numeratorCoefficient i * (v * squareCoefficient units (smallIndex (some i)).val.1)) := by
      rw [basis_square,← map_mul,mul_assoc]
    _ = _ := by
      rw [← hd,numeratorCoefficient,mul_assoc,Units.inv_mul, mul_one]

/-- The exact original field image of the regular numerator. -/
theorem numerator_embedding (i : Fin 4) :
    InfinityOpenFractionField318.openEmbedding units (numerator i) *
      ((InfinityFieldCoordinates318.u units)^3 * CompletedCharacterInfinity318.rawY i) =
      (algebraMap ℚ (InfinityFieldCoordinates318.L units) (xScale i : ℚ))^2 *
        (algebraMap ℚ _ (units 0 : ℚ) - algebraMap ℚ _ (centroid i) *
          (InfinityFieldCoordinates318.u units)^2)^2 := by
  have h := congrArg (InfinityOpenFractionField318.openEmbedding units) (numerator_times_unit i)
  rw [map_mul,CompletedCharacterInfinity318.coefficientUnit_embedding] at h
  have hp : InfinityOpenFractionField318.openEmbedding units
      (algebraMap (Base units) (InfinityRing units)
        (algebraMap ℚ[X] (Base units) (numeratorPolynomial i))) =
      aeval (InfinityFieldCoordinates318.u units) (numeratorPolynomial i) := by
    exact ReciprocalInfinityNormalization318.openEmbedding_on_polynomial units (numeratorPolynomial i)
  rw [hp] at h
  simpa only [numeratorPolynomial,map_mul,map_sub,map_pow,aeval_C,aeval_X] using h

/-- The pullback class is a simple pole in the actual common-open ring,
with its numerator in the original full infinity order. -/
theorem representative_simple_pole (i : Fin 4) :
    OriginalCharacterClassPullbacks318.sourceRepresentative i =
      ContactWholePrincipalReduction318.inclusion units (numerator i) * inverseU units := by
  apply SourceOpenFractionField318.openEmbedding_injective units
  rw [OriginalCharacterClassPullbacks318.sourceRepresentative_embedding,map_mul,
    ContactWholePrincipalReduction318.inclusion,InfinityOverlapLocalization318.toOpen_embedding]
  have hinv : SourceOpenFractionField318.openEmbedding units (inverseU units) =
      (InfinityFieldCoordinates318.u units)⁻¹ :=
    ContactInfinityRegularFractions318.inverse_u_embedding units
  rw [hinv,CompletedCharacterInfinity318.rawX_formula,InfinityFieldCoordinates318.recover_t]
  change (algebraMap ℚ (InfinityFieldCoordinates318.L units) (xScale i : ℚ) *
      (algebraMap ℚ _ (units 0 : ℚ) / (InfinityFieldCoordinates318.u units)^2 -
        algebraMap ℚ _ (centroid i)))^2 / CompletedCharacterInfinity318.rawY i = _
  have h := numerator_embedding i
  field_simp [InfinityFieldCoordinates318.u_ne_zero units,CompletedCharacterInfinity318.rawY_ne_zero i]
  linear_combination -h

/-- Evaluation at the actual infinity point is nonzero, with every original
Weierstrass scaling factor and basis-square unit still present. -/
theorem numerator_coefficient_nonzero (i : Fin 4) :
    InfinityOpenChart318.infinityPoint units (numeratorCoefficient i) ≠ 0 := by
  rw [numeratorCoefficient,map_mul,InfinityOpenChart318.infinityPoint_on_base]
  apply mul_ne_zero
  · simpa only [numeratorPolynomial,eval_mul,eval_pow,eval_sub,eval_C,eval_X,
      zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero] using
      mul_ne_zero (pow_ne_zero 2 (xScale i).ne_zero) (pow_ne_zero 2 (units 0).ne_zero)
  · exact (((denominatorUnit i)⁻¹).isUnit.map (InfinityOpenChart318.infinityPoint units)).ne_zero

end OriginalCharacterSimplePole318
