module
public import ActualTwoDescentPrimaryPadicNaturality318
public section
noncomputable section
namespace ActualTwoDescentDyadicCharacterEndomorphisms318
set_option maxHeartbeats 16000000
open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentPrueferLevelCoordinates318
open ActualTwoDescentPrueferPadicEndomorphisms318

/-- Algebraic characters into the actual rational circle Q/Z. -/
abbrev DyadicCharacter := PrueferAdd →+ AddCircle (1 : ℚ)

def dyadicCharacterEnd (f : DyadicCharacter) : AddMonoid.End PrueferAdd where
  toFun x := Additive.ofMul ⟨Multiplicative.ofAdd (f x),by
    obtain ⟨k,hk⟩ := actual_pruefer_add_primary x
    refine ⟨k,?_⟩
    change (2^k) • f x=0
    rw [←map_nsmul,hk,map_zero]⟩
  map_zero' := by apply Subtype.ext; exact congrArg Multiplicative.ofAdd (map_zero f)
  map_add' x y := by apply Subtype.ext; exact congrArg Multiplicative.ofAdd (map_add f x y)

def prueferEndCharacter (f : AddMonoid.End PrueferAdd) : DyadicCharacter where
  toFun x := (f x).toMul.val.toAdd
  map_zero' := by simp
  map_add' x y := by simp

/-- Every dyadic character has ACTUAL image inside the dyadic subgroup,
so corestriction and the original inclusion are inverse. -/
def dyadicCharacterEndEquiv : DyadicCharacter ≃+ AddMonoid.End PrueferAdd where
  toFun := dyadicCharacterEnd
  invFun := prueferEndCharacter
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl

def dyadicCharacterPadicEquiv : DyadicCharacter ≃+ ℤ_[2] :=
  dyadicCharacterEndEquiv.trans prueferEndPadicEquiv.toAddEquiv

end ActualTwoDescentDyadicCharacterEndomorphisms318
