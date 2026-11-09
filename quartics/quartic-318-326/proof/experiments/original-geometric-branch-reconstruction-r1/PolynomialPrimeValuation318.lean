module
public import RationalFunctionEvenSquare318
public import Mathlib.RingTheory.Valuation.PrimeMultiplicity
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public section
noncomputable section
open scoped BigOperators
namespace PolynomialPrimeValuation318
open Polynomial
variable {F : Type*} [Field F]

@[expose] def enatToInt : ℕ∞ →+o WithTop ℤ where
  toFun n:=n.map (fun m:ℕ=>(m:ℤ))
  map_zero':=rfl
  map_add' a b:=by
    cases a with
    | top => cases b with
      | top => change (⊤:WithTop ℤ)=⊤+⊤; simp
      | coe b => change (⊤:WithTop ℤ)=⊤+(b:ℤ); simp
    | coe a => cases b with
      | top => change (⊤:WithTop ℤ)=(a:ℤ)+⊤; simp
      | coe b => change (((a+b:ℕ):ℤ):WithTop ℤ)=(a:ℤ)+(b:ℤ); norm_cast
  monotone' := by
    intro a b hab
    cases a with
    | top => cases b with
      | top => exact le_refl _
      | coe b => exact (not_le_of_gt (ENat.coe_lt_top b) hab).elim
    | coe a => cases b with
      | top => exact le_top
      | coe b =>
        change ((a:ℤ):WithTop ℤ)≤(b:ℤ)
        have hh:a≤b := by exact_mod_cast hab
        exact_mod_cast hh


@[expose] def integralPlace (q:F[X]) (hq:Prime q) : AddValuation F[X] (WithTop ℤ) :=
  (multiplicity_addValuation hq).map enatToInt rfl

theorem integralPlace_finite (q:F[X]) (hq:Prime q) (u:F[X]) (hu:u≠0) :
    integralPlace q hq u=(multiplicity q u:ℤ) := by
  change enatToInt (emultiplicity q u)=_
  rw [(FiniteMultiplicity.of_prime_left hq hu).emultiplicity_eq_multiplicity]
  all_goals rfl

theorem integralPlace_support (q:F[X]) (hq:Prime q) :
    nonZeroDivisors F[X] ≤ (AddValuation.toValuation (integralPlace q hq)).supp.primeCompl := by
  intro u hu
  have hu0:u≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hu
  change integralPlace q hq u≠⊤
  rw [integralPlace_finite q hq u hu0]
  simp

@[expose] def primePlace (q:F[X]) (hq:Prime q) : AddValuation (RatFunc F) (WithTop ℤ) :=
  AddValuation.ofValuation ((AddValuation.toValuation (integralPlace q hq)).extendToLocalization
    (integralPlace_support q hq) (RatFunc F))

theorem primePlace_integral (q:F[X]) (hq:Prime q) (u:F[X]) :
    primePlace q hq (algebraMap F[X] (RatFunc F) u)=integralPlace q hq u := by
  change (AddValuation.toValuation (integralPlace q hq)).extendToLocalization
    (integralPlace_support q hq) (RatFunc F) (algebraMap F[X] (RatFunc F) u)=_
  rw [Valuation.extendToLocalization_apply_map_apply]
  all_goals rfl

theorem primePlace_multiplicity (q:F[X]) (hq:Prime q) (u:F[X]) (hu:u≠0) :
    primePlace q hq (algebraMap F[X] (RatFunc F) u)=(multiplicity q u:ℤ) := by
  rw [primePlace_integral,integralPlace_finite q hq u hu]

/-- The parity consumer's canonical numerator/denominator order is the actual
extended prime valuation, not a separate ad hoc integer-valued function. -/
theorem primePlace_order (q : F[X]) (hq : Prime q) (x : RatFunc F) (hx : x ≠ 0) :
    primePlace q hq x = (RationalFunctionEvenSquare318.orderAt q x : WithTop ℤ) := by
  conv_lhs => rw [← RatFunc.num_div_denom x]
  rw [(primePlace q hq).map_div,
    primePlace_multiplicity q hq x.num (RatFunc.num_ne_zero hx),
    primePlace_multiplicity q hq x.denom (RatFunc.denom_ne_zero x)]
  change ((multiplicity q x.num : ℤ) : WithTop ℤ) -
    ((multiplicity q x.denom : ℤ) : WithTop ℤ) =
      (((multiplicity q x.num : ℤ) - (multiplicity q x.denom : ℤ)) : WithTop ℤ)
  norm_cast
end PolynomialPrimeValuation318
