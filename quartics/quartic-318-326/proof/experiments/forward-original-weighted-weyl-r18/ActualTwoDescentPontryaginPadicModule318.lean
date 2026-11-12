module
public import ActualTwoDescentPontryaginRationalCharacters318
public section
noncomputable section
namespace ActualTwoDescentPontryaginPadicModule318
set_option maxHeartbeats 16000000
open ActualTwoDescentActualPrimaryCharacters318 ActualTwoDescentSelmerPadicAction318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentPontryaginRationalCharacters318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The actual native Pontryagin scalar is precomposition by the actual
Selmer scalar. The source map is continuous for the actual discrete topology. -/
def nativeDualScalar (n : ℚ) (hn : n ≠ 0) (a : ℤ_[2]) (f : ActualPontryagin n hn) :
    ActualPontryagin n hn where
  toFun x := f (Multiplicative.ofAdd (actualSelmerPadicEnd n hn a (Multiplicative.toAdd x)))
  map_one' := by simp
  map_mul' x y := by simp [map_add,map_mul]
  continuous_toFun := continuous_of_discreteTopology

def actualPontryaginSMul (n : ℚ) (hn : n ≠ 0) : SMul ℤ_[2] (Additive (ActualPontryagin n hn)) :=
  ⟨fun a f => Additive.ofMul (nativeDualScalar n hn a f.toMul)⟩

lemma actual_native_character_scalar (n : ℚ) (hn : n ≠ 0) (a : ℤ_[2]) (f : ActualPontryagin n hn) :
    nativeRationalCharacter n hn (nativeDualScalar n hn a f)=
      (nativeRationalCharacter n hn f).comp (actualSelmerPadicEnd n hn a) := by
  apply AddMonoidHom.ext
  intro x
  rfl

/-- Module axioms are verified for the specified native precomposition
scalar, via the injective actual character comparison. -/
def actualPontryaginPadicModule (n : ℚ) (hn : n ≠ 0) : Module ℤ_[2] (Additive (ActualPontryagin n hn)) := by
  letI := actualPontryaginSMul n hn
  letI := actualCharacterPadicModule n hn
  exact Function.Injective.module (nativeRationalCharacterEquiv n hn).toAddMonoidHom
    (nativeRationalCharacterEquiv n hn).injective
    (fun a f => actual_native_character_scalar n hn a f.toMul)

end ActualTwoDescentPontryaginPadicModule318
