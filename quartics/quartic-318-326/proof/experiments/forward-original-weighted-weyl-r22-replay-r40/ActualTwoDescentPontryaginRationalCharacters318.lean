module
public import ActualTwoDescentPontryaginPrimaryValues318
public section
noncomputable section
namespace ActualTwoDescentPontryaginRationalCharacters318
set_option maxHeartbeats 16000000
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentActualPrimaryCharacters318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentPontryaginPrimaryValues318
open ActualTwoDescentCirclePrimaryPruefer318

def nativeRationalCharacter (n : ℚ) (hn : n ≠ 0) (f : ActualPontryagin n hn) :
    ActualPrimaryCharacters n hn where
  toFun x := (circlePrimaryPrueferEquiv (nativeCircleValue n hn f x)).val.toAdd
  map_zero' := by rw [actual_native_circle_zero,map_one]; rfl
  map_add' x y := by rw [actual_native_circle_add,map_mul]; rfl

def rationalNativeCharacter (n : ℚ) (hn : n ≠ 0) (f : ActualPrimaryCharacters n hn) :
    ActualPontryagin n hn where
  toFun x := (circlePrimaryPrueferEquiv.symm (rationalDyadicValue n hn f (Multiplicative.toAdd x))).val
  map_one' := by rw [actual_rational_dyadic_zero,map_one]; rfl
  map_mul' x y := by rw [actual_rational_dyadic_add,map_mul]; rfl
  continuous_toFun := continuous_of_discreteTopology

lemma actual_native_rational_inverse (n : ℚ) (hn : n ≠ 0) (f : ActualPontryagin n hn) :
    rationalNativeCharacter n hn (nativeRationalCharacter n hn f)=f := by
  apply PontryaginDual.ext
  intro x
  change (circlePrimaryPrueferEquiv.symm
    (circlePrimaryPrueferEquiv (nativeCircleValue n hn f (Multiplicative.toAdd x)))).val=f x
  rw [circlePrimaryPrueferEquiv.symm_apply_apply]
  rfl

lemma actual_rational_native_inverse (n : ℚ) (hn : n ≠ 0) (f : ActualPrimaryCharacters n hn) :
    nativeRationalCharacter n hn (rationalNativeCharacter n hn f)=f := by
  apply AddMonoidHom.ext
  intro x
  change (circlePrimaryPrueferEquiv
    (circlePrimaryPrueferEquiv.symm (rationalDyadicValue n hn f x))).val.toAdd=f x
  rw [circlePrimaryPrueferEquiv.apply_symm_apply]
  rfl

/-- This compares the ACTUAL complex-Circle continuous character group
with the actual rational-circle character group. Continuity is produced
from the actual discrete Selmer topology, not assumed. -/
def nativeRationalCharacterEquiv (n : ℚ) (hn : n ≠ 0) :
    Additive (ActualPontryagin n hn) ≃+ ActualPrimaryCharacters n hn where
  toFun f := nativeRationalCharacter n hn f.toMul
  invFun f := Additive.ofMul (rationalNativeCharacter n hn f)
  left_inv f := actual_native_rational_inverse n hn f.toMul
  right_inv f := actual_rational_native_inverse n hn f
  map_add' f g := by
    apply AddMonoidHom.ext
    intro x
    have he := congrArg (fun z : ActualTwoDescentDyadicPrueferModel318.PrueferTwo => z.val.toAdd)
      (circlePrimaryPrueferEquiv.map_mul (nativeCircleValue n hn f.toMul x) (nativeCircleValue n hn g.toMul x))
    exact he

end ActualTwoDescentPontryaginRationalCharacters318
