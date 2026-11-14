module
public import ActualTwoDescentDiscreteSelmerDual318
public section
noncomputable section
namespace ActualTwoDescentPontryaginPrimaryValues318
set_option maxHeartbeats 16000000
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentSelmerPadicAction318
open ActualTwoDescentCirclePrimaryInvolutions318 ActualTwoDescentDiscreteSelmerDual318
open ActualTwoDescentActualPrimaryCharacters318 ActualTwoDescentDyadicPrueferModel318

def nativeCircleValue (n : ℚ) (hn : n ≠ 0) (f : ActualPontryagin n hn)
    (x : actualPrimarySelmer n hn) : CirclePrimary := ⟨f (Multiplicative.ofAdd x),by
  obtain ⟨k,hk⟩ := actual_selmer_primary n hn x
  refine ⟨k,?_⟩
  have hp : (Multiplicative.ofAdd x : DiscreteSelmer n hn)^(2^k)=1 := congrArg Multiplicative.ofAdd hk
  rw [←map_pow,hp,map_one]⟩

lemma actual_native_circle_zero (n : ℚ) (hn : n ≠ 0) (f : ActualPontryagin n hn) :
    nativeCircleValue n hn f 0=1 := Subtype.ext (map_one f)
lemma actual_native_circle_add (n : ℚ) (hn : n ≠ 0) (f : ActualPontryagin n hn)
    (x y : actualPrimarySelmer n hn) :
    nativeCircleValue n hn f (x+y)=nativeCircleValue n hn f x*nativeCircleValue n hn f y :=
  Subtype.ext (map_mul f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

def rationalDyadicValue (n : ℚ) (hn : n ≠ 0) (f : ActualPrimaryCharacters n hn)
    (x : actualPrimarySelmer n hn) : PrueferTwo := ⟨Multiplicative.ofAdd (f x),by
  obtain ⟨k,hk⟩ := actual_selmer_primary n hn x
  refine ⟨k,?_⟩
  change (2^k) • f x=0
  rw [←map_nsmul,hk,map_zero]⟩

lemma actual_rational_dyadic_zero (n : ℚ) (hn : n ≠ 0) (f : ActualPrimaryCharacters n hn) :
    rationalDyadicValue n hn f 0=1 := Subtype.ext (congrArg Multiplicative.ofAdd (map_zero f))
lemma actual_rational_dyadic_add (n : ℚ) (hn : n ≠ 0) (f : ActualPrimaryCharacters n hn)
    (x y : actualPrimarySelmer n hn) :
    rationalDyadicValue n hn f (x+y)=rationalDyadicValue n hn f x*rationalDyadicValue n hn f y :=
  Subtype.ext (congrArg Multiplicative.ofAdd (map_add f x y))

end ActualTwoDescentPontryaginPrimaryValues318
