module
public import PELPrimePeriodIsogenies318
public section
noncomputable section
namespace PELPrimeIsogenyFibers318
open PELPrimeNormalizerData318 PELPositiveNormPeriodMap318 PELPrimePeriodIsogenies318
open PELComplexPeriodSurface318
set_option maxHeartbeats 1200000

/-- Translation by an ACTUAL preimage identifies the entire fiber of an
additive map with its actual kernel, not merely their cardinalities. -/
@[expose] def additiveFiberEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (a : A) (b : B) (ha : f a=b) : f.ker ≃ {x : A // f x=b} where
  toFun x := ⟨x.val+a,by rw [map_add,x.property,zero_add,ha]⟩
  invFun y := ⟨y.val-a,by rw [map_sub,y.property,ha,sub_self]⟩
  left_inv x := by apply Subtype.ext; exact add_sub_cancel_right x.val a
  right_inv y := by apply Subtype.ext; exact sub_add_cancel y.val a

variable (i : Fin 4) (τ : ℂ) (hτ : 0<τ.im)
@[expose] def primeFiberEquiv (p : Surface τ) :
    (primeMap i τ hτ).ker ≃ {q : Surface (translated (primeElement i) τ) // primeMap i τ hτ q=p} :=
  additiveFiberEquiv (primeMap i τ hτ) ((primeMap_surjective i τ hτ p).choose) p
    (primeMap_surjective i τ hτ p).choose_spec

noncomputable instance primeFiberFintype (p : Surface τ) :
    Fintype {q : Surface (translated (primeElement i) τ) // primeMap i τ hτ q=p} :=
  Fintype.ofEquiv (primeMap i τ hτ).ker (primeFiberEquiv i τ hτ p)

/-- EVERY actual fiber has exactly p² points. Together with the earlier
original-atlas holomorphy and surjectivity this is an analytic isogeny endpoint,
not a statement about an unconstructed algebraic isogeny degree. -/
theorem every_fiber_card (p : Surface τ) :
    Fintype.card {q : Surface (translated (primeElement i) τ) // primeMap i τ hτ q=p}=(prime i)^2 := by
  rw [←Fintype.card_congr (primeFiberEquiv i τ hτ p)]
  exact prime_kernel_card i τ hτ
end PELPrimeIsogenyFibers318
