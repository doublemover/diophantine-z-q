module
public import PELOriginalCM210FullIntegralCoordinates318
public section
noncomputable section
namespace PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210IntegralConjugation318
abbrev O := NumberField.RingOfIntegers K
@[expose] def nativeMap : R→+*O where
  toFun z := ⟨intMap z,image_integral z⟩
  map_one' := by apply NumberField.RingOfIntegers.ext; exact intMap.map_one
  map_zero' := by apply NumberField.RingOfIntegers.ext; exact intMap.map_zero
  map_add' x y := by apply NumberField.RingOfIntegers.ext; exact intMap.map_add x y
  map_mul' x y := by apply NumberField.RingOfIntegers.ext; exact intMap.map_mul x y
lemma nativeMap_injective : Function.Injective nativeMap := by
  intro x y h
  apply intMap_injective
  exact congrArg (fun z:O => (z:K)) h
lemma nativeMap_surjective : Function.Surjective nativeMap := by
  intro z
  obtain ⟨r,hr⟩ := (PELOriginalCM210FullIntegralCoordinates318.integral_iff_image (z:K)).mp z.property
  exact ⟨r,NumberField.RingOfIntegers.ext hr⟩
/-- The full native integer ring, not merely the displayed quadratic suborder. -/
@[expose] def integerEquiv : R≃+*O :=
  RingEquiv.ofBijective nativeMap ⟨nativeMap_injective,nativeMap_surjective⟩
lemma integerEquiv_value (z:R) : (integerEquiv z:K)=intMap z := rfl
lemma original_integer_realization (z:R) :
    PELInertiaQuadraticEmbeddings318.realization 4 (integerEquiv z:K)=
      PELInertiaQuadraticEmbeddings318.realization 4 (intMap z) := rfl
lemma every_integer_in_original_image (z:O) :
    ∃r:R,PELInertiaQuadraticEmbeddings318.realization 4 (z:K)=
      PELInertiaQuadraticEmbeddings318.realization 4 (intMap r) := by
  obtain ⟨r,hr⟩ := integerEquiv.surjective z
  exact ⟨r,by rw [←hr]; rfl⟩

end PELOriginalCM210NativeIntegerOrder318
