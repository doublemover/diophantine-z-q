module
public import PELCMConstituentFieldEmbeddings318
public section
noncomputable section
namespace PELCMConstituentNativeOrderEmbeddings318
open PELCMQuadraticConstituentFields318 PELCMConstituentFieldEmbeddings318
open PELCMQuadraticConstituentOrders318 PELCMQuadraticIntegralTraceData318
open PELOriginalCM210RadicalTower318 PELCMShiftedRadicalGenerators318
abbrev OH := NumberField.RingOfIntegers H
/-- Restrict the actual field embedding to the full native integer ring. -/
@[expose] def nativeEmbedding (i : Fin 4) : Integers i →+* OH where
  toFun z := ⟨embedding i z, map_isIntegral_int (embedding i).toRingHom z.property⟩
  map_zero' := by apply NumberField.RingOfIntegers.ext; exact (embedding i).map_zero
  map_one' := by apply NumberField.RingOfIntegers.ext; exact (embedding i).map_one
  map_add' z w := by apply NumberField.RingOfIntegers.ext; exact (embedding i).map_add z w
  map_mul' z w := by apply NumberField.RingOfIntegers.ext; exact (embedding i).map_mul z w
lemma nativeEmbedding_value (i : Fin 4) (z : Integers i) :
    (nativeEmbedding i z : H) = embedding i (z : Field i) := rfl
lemma nativeEmbedding_injective (i : Fin 4) : Function.Injective (nativeEmbedding i) := by
  intro z w he
  apply NumberField.RingOfIntegers.ext
  apply embedding_injective i
  exact congrArg (fun x : OH => (x : H)) he
lemma full_order_square (i : Fin 4) (z : R (a i) (b i)) :
    (nativeEmbedding i (fullIntegerEquiv i z) : H) =
      embedding i (intMap (a i) (b i) z) := rfl
lemma full_order_coordinates (i : Fin 4) (z : R (a i) (b i)) :
    (nativeEmbedding i (fullIntegerEquiv i z) : H) =
      algebraMap ℚ H (z.re : ℚ) + algebraMap ℚ H (z.im : ℚ) * shifted i := by
  rw [full_order_square, embedding_coordinates]
  rfl
lemma shifted_integral (i : Fin 4) : IsIntegral ℤ (shifted i) := by
  rw [← embedding_omega]
  exact map_isIntegral_int (embedding i).toRingHom (omega_integral (a i) (b i))
lemma every_native_image_integral (i : Fin 4) (z : Integers i) :
    IsIntegral ℤ (embedding i (z : Field i)) := (nativeEmbedding i z).property
end PELCMConstituentNativeOrderEmbeddings318
