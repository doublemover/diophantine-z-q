module
public import CTNativePadicUnitNormalization318
public import ActualTwoDescentSquareClassQuotient318
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.Prod
import all ActualTwoDescentSquareClassQuotient318
import all CTNativePadicUnitNormalization318
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public section

noncomputable section
namespace CTNativePadicValuationBit318

open CTNativePadicUnitNormalization318 ActualTwoDescentSquareClassQuotient318

abbrev Bit := ZMod 2

variable (p : ℕ) [Fact p.Prime]

def valuationBit : ℚ_[p]ˣ →* Multiplicative Bit where
  toFun x := Multiplicative.ofAdd ((x:ℚ_[p]).valuation:Bit)
  map_one' := by
    change ((↑(1:ℚ_[p]ˣ):ℚ_[p]).valuation:Bit)=0
    rw [Units.val_one,Padic.valuation_one,Int.cast_zero]
  map_mul' x y := by
    change (((↑(x*y):ℚ_[p]).valuation:ℤ):Bit) =
      ((x:ℚ_[p]).valuation:Bit)+((y:ℚ_[p]).valuation:Bit)
    rw [Units.val_mul,Padic.valuation_mul x.ne_zero y.ne_zero,Int.cast_add]

def residueUnits : ℚ_[p]ˣ →* (ZMod p)ˣ :=
  (Units.map (PadicInt.toZMod (p:=p)).toMonoidHom).comp (normalizeHom p)

/-- Common F₂ factorization of a unit-coordinate hom through the literal
squareclass quotient. Both source and target quotient are the actual types. -/
def liftBitCoordinates {V : Type*} [AddCommGroup V] [Module Bit V]
    (f : ℚ_[p]ˣ →* Multiplicative V) : SquareClass ℚ_[p] →* Multiplicative V :=
  QuotientGroup.lift (powMonoidHom (α:=ℚ_[p]ˣ) 2).range f (by
    rintro _ ⟨u,rfl⟩
    change f (u^2)=1
    rw [map_pow]
    change 2 • (f u).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul Bit]
    change (2:Bit) • (f u).toAdd=0
    rw [show (2:Bit)=0 from rfl,zero_smul])

theorem liftBitCoordinates_on_value {V : Type*} [AddCommGroup V] [Module Bit V]
    (f : ℚ_[p]ˣ →* Multiplicative V) (x : ℚ_[p]) (hx : x≠0) :
    liftBitCoordinates p f (classOf x hx)=f (Units.mk0 x hx) := by
  change liftBitCoordinates p f (QuotientGroup.mk (Units.mk0 x hx))=_
  rfl

/-- Signed even valuation and a square unit part give an actual root. -/
theorem square_of_valuationBit_zero_and_norm_square (x : ℚ_[p]) (hx : x≠0)
    (hV : (x.valuation:Bit)=0) (r : ℚ_[p]) (hr : r≠0)
    (he : normalizedField p (Units.mk0 x hx)=r^2) :
    ∃ s : ℚ_[p], s≠0 ∧ x=s^2 := by
  obtain ⟨m,hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.valuation 2).mp hV
  have hm2 : x.valuation=m+m := by omega
  refine ⟨(p:ℚ_[p])^m*r,mul_ne_zero (zpow_ne_zero _ (padic_prime_ne p)) hr,?_⟩
  calc
    x=(p:ℚ_[p])^x.valuation*normalizedField p (Units.mk0 x hx) :=
      field_factorization p (Units.mk0 x hx)
    _=_ := by rw [hm2,zpow_add₀ (padic_prime_ne p),he]; ring

theorem coordinates_injective_of_kernel_square {V : Type*} [AddCommGroup V]
    (f : SquareClass ℚ_[p] →* Multiplicative V)
    (hSquare : ∀ (x : ℚ_[p]) (hx : x≠0), f (classOf x hx)=1 →
      ∃ s : ℚ_[p], s≠0 ∧ x=s^2) : Function.Injective f := by
  have hker (q : SquareClass ℚ_[p]) (h : f q=1) : q=1 := by
    revert h
    refine QuotientGroup.induction_on q ?_
    intro u he
    have hm : Units.mk0 (u:ℚ_[p]) u.ne_zero=u := by ext; rfl
    have hU : classOf (u:ℚ_[p]) u.ne_zero=QuotientGroup.mk u := by rw [classOf,hm]
    rw [←hU] at he ⊢
    obtain ⟨s,hs,hS⟩ := hSquare (u:ℚ_[p]) u.ne_zero he
    rw [← class_of_one]
    exact (class_of_eq_iff _ _ _ _).mpr ⟨s,hs,by simpa only [one_mul] using hS⟩
  intro a b h
  apply div_eq_one.mp
  apply hker
  rw [map_div,h,div_self']

theorem normalizedInteger_valuative_unit (x : ℚ_[p]ˣ) (U : ℤ_[p])
    (he : (x:ℚ_[p])=(U:ℚ_[p])) (hv : (x:ℚ_[p]).valuation=0) :
    normalizedInteger p x=U := by
  apply PadicInt.ext
  change normalizedField p x=(U:ℚ_[p])
  exact (normalized_of_valuation_zero p x hv).trans he

theorem normalizedInteger_prime :
    normalizedInteger p (Units.mk0 (p:ℚ_[p]) (padic_prime_ne p))=1 := by
  apply PadicInt.ext
  change normalizedField p (Units.mk0 (p:ℚ_[p]) (padic_prime_ne p))=1
  exact normalized_prime_field p

end CTNativePadicValuationBit318

#print axioms CTNativePadicValuationBit318.valuationBit
#print axioms CTNativePadicValuationBit318.liftBitCoordinates_on_value
