module
public import PELCMQuadraticConstituentFields318
public import PELCMQuadraticNativeDiscriminant318
public import PELCMOddQuadraticFullCoordinates318
public import PELCMMinusTwoFullCoordinates318
public section
noncomputable section
namespace PELCMQuadraticConstituentOrders318
open PELCMQuadraticIntegralTraceData318 PELCMQuadraticNativeIntegerOrder318
open PELCMQuadraticConstituentFields318
/-- The full coordinate premise is constructed for every one of the four rows. -/
lemma full_coordinates (i:Fin 4) : Coordinates (a i) (b i) := by
  fin_cases i
  · exact PELCMMinusTwoFullCoordinates318.integer_coordinates
  · exact PELCMOddQuadraticFullCoordinates318.integer_coordinates 0
  · exact PELCMOddQuadraticFullCoordinates318.integer_coordinates 1
  · exact PELCMOddQuadraticFullCoordinates318.integer_coordinates 2
@[expose] def fullIntegerEquiv (i:Fin 4) : R (a i) (b i)≃+*Integers i :=
  integerEquiv (a i) (b i) (full_coordinates i)
lemma fullIntegerEquiv_value (i:Fin 4) (z:R (a i) (b i)) :
    (fullIntegerEquiv i z:Field i)=intMap (a i) (b i) z := rfl
lemma native_discriminant (i:Fin 4) : NumberField.discr (Field i)=discriminant i :=
  (PELCMQuadraticNativeDiscriminant318.native_discriminant (a i) (b i)
    (full_coordinates i)).trans (coefficient_discriminant i)
lemma all_four_discriminants :
    NumberField.discr (Field 0)=-8 ∧ NumberField.discr (Field 1)=-3 ∧
    NumberField.discr (Field 2)=5 ∧ NumberField.discr (Field 3)=-7 :=
  ⟨native_discriminant 0,native_discriminant 1,native_discriminant 2,native_discriminant 3⟩
lemma integral_iff_coordinates (i:Fin 4) (z:Field i) :
    IsIntegral ℤ z ↔ ∃r s:ℤ,z.re=(r:ℚ) ∧ z.im=(s:ℚ) := by
  constructor
  · exact full_coordinates i z
  · rintro ⟨r,s,hr,hs⟩
    have he : intMap (a i) (b i) (⟨r,s⟩:R (a i) (b i))=z :=
      QuadraticAlgebra.ext hr.symm hs.symm
    rw [←he]
    exact image_integral _ _ _
end PELCMQuadraticConstituentOrders318
