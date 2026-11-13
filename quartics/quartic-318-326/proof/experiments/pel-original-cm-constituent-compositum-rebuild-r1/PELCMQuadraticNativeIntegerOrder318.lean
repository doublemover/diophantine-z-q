module
public import PELCMQuadraticIntegralTraceData318
public section
noncomputable section
namespace PELCMQuadraticNativeIntegerOrder318
open PELCMQuadraticIntegralTraceData318
variable (a b:ℤ) [Fact (∀x:ℚ,x^2≠(a:ℚ)+(b:ℚ)*x)]
instance : NumberField (F a b) where
abbrev O := NumberField.RingOfIntegers (F a b)
@[expose] def nativeMap : R a b→+*O a b where
  toFun z := ⟨intMap a b z,image_integral a b z⟩
  map_one' := by apply NumberField.RingOfIntegers.ext; exact (intMap a b).map_one
  map_zero' := by apply NumberField.RingOfIntegers.ext; exact (intMap a b).map_zero
  map_add' x y := by apply NumberField.RingOfIntegers.ext; exact (intMap a b).map_add x y
  map_mul' x y := by apply NumberField.RingOfIntegers.ext; exact (intMap a b).map_mul x y
lemma nativeMap_injective : Function.Injective (nativeMap a b) := by
  intro z w h
  apply intMap_injective a b
  exact congrArg (fun z:O a b=>(z:F a b)) h
@[expose] def Coordinates : Prop :=
  ∀z:F a b,IsIntegral ℤ z→∃r s:ℤ,z.re=(r:ℚ) ∧ z.im=(s:ℚ)
lemma nativeMap_surjective (hcoords:Coordinates a b) : Function.Surjective (nativeMap a b) := by
  intro z
  obtain ⟨r,s,hr,hs⟩ := hcoords z z.property
  exact ⟨⟨r,s⟩,NumberField.RingOfIntegers.ext (QuadraticAlgebra.ext hr.symm hs.symm)⟩
@[expose] def integerEquiv (hcoords:Coordinates a b) : R a b≃+*O a b :=
  RingEquiv.ofBijective (nativeMap a b) ⟨nativeMap_injective a b,nativeMap_surjective a b hcoords⟩
@[expose] def integerAlgEquiv (hcoords:Coordinates a b) : R a b≃ₐ[ℤ]O a b where
  __ := integerEquiv a b hcoords
  commutes' n := map_intCast (integerEquiv a b hcoords) n
lemma integerEquiv_value (hcoords:Coordinates a b) (z:R a b) :
    (integerEquiv a b hcoords z:F a b)=intMap a b z := rfl
end PELCMQuadraticNativeIntegerOrder318
