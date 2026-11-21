module
public import CTOriginalBadPrimeSignedCodes318
import all CTOriginalBadPrimeSignedCodes318
import all CTOriginalPrimeMonomials318
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
public section

noncomputable section

namespace CTGlobalSupportedSquareclassCode318

open ActualNaturalAllPlacesFinite318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentSquareClassQuotient318
open scoped BigOperators

private instance supportPrime {n : ℕ} (i : Support n) : Fact i.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors i.property⟩

def scalar (n : ℕ) (a : Code n) : ℚ :=
  (-1:ℚ)^a.1.val*(monomial (fun i : Support n => i.val) a.2 : ℚ)

theorem scalar_ne (n : ℕ) (a : Code n) : scalar n a≠0 := by
  have hm : 0 < (monomial (fun i : Support n => i.val) a.2 : ℚ) := by
    exact_mod_cast monomial_pos (fun i : Support n => i.val) a.2
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hm.ne'

theorem supportedClass_value (n : ℕ) (a : Code n) :
    supportedClass n a=classOf (scalar n a) (scalar_ne n a) := rfl

theorem scalar_pos_iff (n : ℕ) (a : Code n) :
    0<scalar n a ↔ a.1=0 := by
  have hp : ∀ e : ZMod 2, 0<(-1:ℚ)^e.val ↔ e=0 := by decide
  have hm : 0 < (monomial (fun i : Support n => i.val) a.2 : ℚ) := by
    exact_mod_cast monomial_pos (fun i : Support n => i.val) a.2
  constructor
  · intro h
    apply (hp a.1).mp
    by_contra hε
    exact (not_le_of_gt h) (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hε) hm.le)
  · intro h
    exact mul_pos ((hp a.1).mpr h) hm

theorem scalar_valuation_bit (n : ℕ) (a : Code n) (i : Support n) :
    (padicValRat i.val (scalar n a):ZMod 2)=a.2 i := by
  have hm : 0 < (monomial (fun i : Support n => i.val) a.2 : ℚ) := by
    exact_mod_cast monomial_pos (fun i : Support n => i.val) a.2
  unfold scalar
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hm.ne',padicValRat.pow]
  simp only [padicValRat.neg,padicValRat.one,mul_zero,zero_mul,zero_add]
  exact actual_monomial_valuation_bit (fun i : Support n => i.val)
    (fun _ _ h => Subtype.ext h) a.2 i

/-- No two signed support codes represent the same literal squareclass.
Sign is detected at the real coordinate; each bit by its own prime. -/
theorem supportedClass_injective (n : ℕ) : Function.Injective (supportedClass n) := by
  intro a b h
  rw [supportedClass_value,supportedClass_value] at h
  obtain ⟨r,hr,he⟩ := (class_of_eq_iff _ _ _ _).mp h
  have hPos : 0<scalar n a ↔ 0<scalar n b := by
    constructor
    · intro hA
      by_contra hB
      have hNeg : scalar n a≤0 := by
        rw [he]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hB) (sq_nonneg r)
      exact (not_le_of_gt hA) hNeg
    · intro hB
      rw [he]
      exact mul_pos hB (sq_pos_of_ne_zero hr)
  have hSign : a.1=b.1 := by
    have hTwo : ∀ e d : ZMod 2, (e=0 ↔ d=0) → e=d := by decide
    exact hTwo a.1 b.1 ((scalar_pos_iff n a).symm.trans (hPos.trans (scalar_pos_iff n b)))
  refine Prod.ext hSign (funext fun i => ?_)
  have hV := congrArg (fun t : ℚ => (padicValRat i.val t:ZMod 2)) he
  rw [padicValRat.mul (scalar_ne n b) (pow_ne_zero 2 hr),padicValRat.pow] at hV
  simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,show (2:ZMod 2)=0 from rfl,
    zero_mul,mul_zero,add_zero,scalar_valuation_bit] using hV

private theorem val_carry : ∀ e d : ZMod 2,
    e.val+d.val=(e+d).val+(e*d).val*2 := by decide

private theorem power_carry {M : Type*} [Monoid M] (x : M) (e d : ZMod 2) :
    x^e.val*x^d.val=x^(e+d).val*(x^(e*d).val)^2 := by
  rw [←pow_add,←pow_mul,←pow_add,val_carry e d]

private theorem monomial_carry {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℕ)
    (u v : I → ZMod 2) :
    monomial p u*monomial p v=monomial p (u+v)*(monomial p (u*v))^2 := by
  calc
    _=∏ i : I, p i^(u i).val*p i^(v i).val := by
      unfold monomial
      exact (Finset.prod_mul_distrib).symm
    _=∏ i : I, p i^((u+v) i).val*(p i^((u*v) i).val*p i^((u*v) i).val) := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Pi.add_apply,Pi.mul_apply,pow_two] using power_carry (p i) (u i) (v i)
    _=_ := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,pow_two] <;> rfl

private theorem scalar_carry (n : ℕ) (a b : Code n) :
    scalar n a*scalar n b=scalar n (a+b)*(scalar n (a*b))^2 := by
  let p : Support n → ℕ := fun i => i.val
  have h1 := power_carry (-1:ℚ) a.1 b.1
  have hN := congrArg (fun k : ℕ => (k:ℚ)) (monomial_carry p a.2 b.2)
  simp only [Nat.cast_mul,Nat.cast_pow] at hN
  change ((-1:ℚ)^a.1.val*(monomial p a.2:ℚ))*((-1:ℚ)^b.1.val*(monomial p b.2:ℚ)) =
    ((-1:ℚ)^(a.1+b.1).val*(monomial p (a.2+b.2):ℚ))*
      (((-1:ℚ)^(a.1*b.1).val*(monomial p (a.2*b.2):ℚ))^2)
  calc
    _=((-1:ℚ)^a.1.val*(-1:ℚ)^b.1.val)*((monomial p a.2:ℚ)*(monomial p b.2:ℚ)) := by ring
    _=_ := by rw [h1,hN]; ring

theorem supportedClass_add (n : ℕ) (a b : Code n) :
    supportedClass n (a+b)=supportedClass n a*supportedClass n b := by
  simp only [supportedClass_value]
  rw [←class_of_mul]
  symm
  exact (class_of_eq_iff _ _ _ _).mpr ⟨scalar n (a*b),scalar_ne n (a*b),scalar_carry n a b⟩

theorem supportedClass_zero (n : ℕ) : supportedClass n 0=1 := by
  rw [supportedClass_value,←class_of_one]
  apply (class_of_eq_iff _ _ _ _).mpr
  refine ⟨1,one_ne_zero,?_⟩
  simp [scalar,monomial]

def supportedCodeHom (n : ℕ) : Code n →+ Additive (SquareClass ℚ) where
  toFun a := Additive.ofMul (supportedClass n a)
  map_zero' := supportedClass_zero n
  map_add' := supportedClass_add n

theorem supportedCodeHom_injective (n : ℕ) : Function.Injective (supportedCodeHom n) :=
  supportedClass_injective n

end CTGlobalSupportedSquareclassCode318

#print axioms CTGlobalSupportedSquareclassCode318.supportedClass_injective
#print axioms CTGlobalSupportedSquareclassCode318.supportedCodeHom_injective
