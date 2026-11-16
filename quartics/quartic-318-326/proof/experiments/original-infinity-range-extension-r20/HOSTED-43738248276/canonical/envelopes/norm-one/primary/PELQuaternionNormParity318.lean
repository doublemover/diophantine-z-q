module
public import PELInertiaFivefoldRelation318
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public section
noncomputable section
namespace PELQuaternionNormParity318
open PELQuaternionAlgebra318 PELQuaternionAnisotropy318
open PELPrimeNormalizerData318
set_option maxHeartbeats 1200000

instance primeFact (j : Fin 4) : Fact (Nat.Prime (prime j)) :=
  ⟨by fin_cases j <;> norm_num [prime]⟩

theorem prime_injective : Function.Injective prime := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [prime]

theorem norm_mul (x y : B) : reducedNorm (x*y)=reducedNorm x*reducedNorm y := by
  simp [reducedNorm] <;> ring

theorem norm_scalar (q : ℚ) : reducedNorm (algebraMap ℚ B q)=q^2 := by
  simp [reducedNorm,QuaternionAlgebra.algebraMap_eq]

/-- Actual prime-by-prime reduced-norm parity, including negative rational
valuations, on units of the original quaternion algebra. -/
@[expose] def parity (u : Bˣ) : InertiaLabels318.V :=
  fun j => (padicValRat (prime j) (reducedNorm (u:B)):ZMod 2)

theorem parity_one : parity 1=0 := by
  ext j
  simp [parity,reducedNorm]

theorem parity_mul (u v : Bˣ) : parity (u*v)=parity u+parity v := by
  ext j
  change (padicValRat (prime j) (reducedNorm ((u:B)*(v:B))):ZMod 2)=_
  rw [norm_mul,padicValRat.mul (reducedNorm_ne_zero _ u.ne_zero)
    (reducedNorm_ne_zero _ v.ne_zero),Int.cast_add] <;> rfl

@[expose] def parityHom : Bˣ →* Multiplicative InertiaLabels318.V where
  toFun u := Multiplicative.ofAdd (parity u)
  map_one' := parity_one
  map_mul' := parity_mul

/-- Each original prime representative gives the corresponding basis bit. -/
theorem parity_prime (i j : Fin 4) :
    parity (rationalUnit i) j=if i=j then 1 else 0 := by
  change (padicValRat (prime j) (reducedNorm (element i)):ZMod 2)=_
  rw [element_norm]
  by_cases hij : i=j
  · subst i
    rw [padicValRat.self (Nat.Prime.one_lt (Fact.out : Nat.Prime (prime j)))]
    simp
  · have hp : prime j≠prime i := fun h => hij (prime_injective h.symm)
    rw [padicValRat.of_nat,padicValNat_primes hp]
    simp [hij]

@[expose] def scalarUnit (q : ℚˣ) : Bˣ :=
  Units.map (algebraMap ℚ B).toMonoidHom q

/-- Rational scalars vanish because their reduced norms are exact squares. -/
theorem parity_scalar (q : ℚˣ) : parity (scalarUnit q)=0 := by
  ext j
  change (padicValRat (prime j) (reducedNorm (algebraMap ℚ B (q:ℚ))):ZMod 2)=0
  rw [norm_scalar,padicValRat.pow]
  push_cast
  rw [show (2:ZMod 2)=0 from ZMod.natCast_self 2,zero_mul]

@[expose] def integralUnit (u : PELPrincipalOrderCoordinates318.orderˣ) : Bˣ :=
  Units.map PELPrincipalOrderCoordinates318.order.subtype.toMonoidHom u

theorem parity_norm_one (u : PELPrincipalOrderCoordinates318.orderˣ)
    (hu : reducedNorm ((u:PELPrincipalOrderCoordinates318.order):B)=1) :
    parity (integralUnit u)=0 := by
  ext j
  change (padicValRat (prime j) (reducedNorm
    ((u:PELPrincipalOrderCoordinates318.order):B)):ZMod 2)=0
  rw [hu,padicValRat.one]
  norm_num

/-- Every original binary label is realized by an actual original prime word.
This is surjectivity, not a postulated normalizer quotient of order16. -/
theorem parity_word (v : InertiaLabels318.V) :
    parity (PELInertiaPrimeWord318.word v)=v := by
  have bit (z : ZMod 2) : (if z=0 then (0:ZMod 2) else 1)=z := by
    classical
    by_cases hz : z=0
    · simp only [hz,ite_true]
    · have hv : z.val=1 := by
        have hlt:=ZMod.val_lt z
        have hne : z.val≠0 := fun h => hz ((ZMod.val_eq_zero z).mp h)
        omega
      have he : z=1 := (ZMod.val_injective 2) (by
        simpa only [ZMod.val_one_eq_one_mod] using hv)
      rw [if_neg hz]
      exact he.symm
  have term (i j : Fin 4) :
      parity (if v i=0 then 1 else rationalUnit i) j=if i=j then v i else 0 := by
    by_cases hz : v i=0
    · simp [hz,parity_one]
    · have hv : v i=1 := by
        simpa only [if_neg hz] using (bit (v i)).symm
      simp [hz,parity_prime,hv]
  unfold PELInertiaPrimeWord318.word
  simp only [parity_mul]
  ext j
  simp only [Pi.add_apply,term]
  fin_cases j <;> simp

theorem parity_surjective : Function.Surjective parityHom := by
  intro v
  exact ⟨PELInertiaPrimeWord318.word (Multiplicative.toAdd v),parity_word _⟩
end PELQuaternionNormParity318
