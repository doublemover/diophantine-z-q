module
public import PELLevelThreeCoordinates318
public section
noncomputable section
namespace PELLevelThreeAlternatingPair318
open PELOrderReductionThree318 PELPrincipalOrderCoordinates318 PELLevelThreeCoordinates318
set_option maxHeartbeats 1200000

/-- Alternating pairing on the ACTUAL O/3O, with the sign of the positive
period Riemann form explicitly retained. -/
@[expose] def pair (a b : QuotientOrder) : F3 :=
  orientedForm (quotientCoordinates a) (quotientCoordinates b)

theorem original_pair (a b : Coordinates) :
    pair (moduloThree.mk' (coordinatesEquiv a)) (moduloThree.mk' (coordinatesEquiv b))=
      (-(integralForm a b):ℤ) := by
  rw [pair,original_coordinates,original_coordinates,original_form]

theorem alternating (a : QuotientOrder) : pair a a=0 := form_alternating _
theorem add_left (a b c : QuotientOrder) : pair (a+b) c=pair a c+pair b c := by
  simp only [pair,map_add,form_add_left]
theorem add_right (a b c : QuotientOrder) : pair a (b+c)=pair a b+pair a c := by
  simp only [pair,map_add,form_add_right]

theorem nondegenerate (a : QuotientOrder) (ha : ∀ b, pair a b=0) : a=0 := by
  apply quotientCoordinates.injective
  rw [map_zero]
  apply form_nondegenerate
  intro b
  obtain ⟨b,rfl⟩ := quotientCoordinates.surjective b
  exact ha b

/-- The original positive Rosati preserves the actual order. -/
@[expose] def orderRosati (a : order) : order :=
  ⟨PELQuaternionAlgebra318.rosati a,rosati_mem a a.property⟩

theorem orderRosati_coordinates (a : Coordinates) :
    orderRosati (coordinatesEquiv a)=coordinatesEquiv (involution a) := by
  apply Subtype.ext
  exact (embed_rosati a).symm

theorem integral_adjoint (a b c : Coordinates) :
    integralForm (product a b) c=integralForm b (product (involution a) c) := by
  simp [integralForm,product,involution] <;> ring

/-- The actual left order action has the SAME Rosati adjoint after reduction. -/
theorem original_adjoint (a : order) (b c : QuotientOrder) :
    pair (moduloThree.mk' a*b) c=pair b (moduloThree.mk' (orderRosati a)*c) := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective a
  obtain ⟨b,rfl⟩ := moduloThree.mk'_surjective b
  obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective b
  obtain ⟨c,rfl⟩ := moduloThree.mk'_surjective c
  obtain ⟨c,rfl⟩ := coordinatesEquiv.surjective c
  rw [orderRosati_coordinates,← map_mul,← map_mul,← coordinates_mul,← coordinates_mul,
    original_pair,original_pair,integral_adjoint]
end PELLevelThreeAlternatingPair318
