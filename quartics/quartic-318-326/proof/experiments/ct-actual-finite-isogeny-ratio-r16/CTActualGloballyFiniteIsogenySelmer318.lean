module
public import CTActualGoodIsogenyImages318
public import CTGlobalSupportedLocalization318
public import OriginalCasselsNaturalPrimeValuation318
import all CTGlobalSupportedSquareclassCode318
import all CTOriginalPrimeMonomials318
import all CTActualDualConnecting318
import all CTActualQuadraticHOne318
import OriginalCasselsOddUnitSquare318
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section
noncomputable section

namespace CTActualGloballyFiniteIsogenySelmer318

open CTActualGoodIsogenyImages318 CTActualDualConnecting318 CTActualQuadraticHOne318
open CTGlobalSupportedSquareclassCode318
open ActualNaturalAllPlacesFinite318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open OriginalSelectedCasselsParity318 OriginalCasselsDyadicXClass318
open OriginalCasselsNaturalPrimeValuation318 OriginalCasselsOddUnitSquare318
open scoped BigOperators

inductive Side
  | forward | reverse

/-- Literal local x-class images on the two unchanged point groups.
The reverse side is the actual continuous connecting range by the
separate theorem below. The forward scalar description is already green. -/
def occurs (e : Side) (K : Type) [Field K] [CharZero K] [DecidableEq K]
    (n : K) (hn : n≠0) (c : SquareClass K) : Prop :=
  match e with
  | .forward => ∃ P : TargetPoint n, targetClass P=c
  | .reverse => ∃ P : Point n, reverseValue K n hn P=c

theorem reverse_occurs_iff_actual_range (K : Type) [Field K] [CharZero K] [DecidableEq K]
    (n : K) (hn : n≠0) (c : SquareClass K) :
    occurs .reverse K n hn c ↔
      (scalarKummer K c).toAdd ∈ (connecting K n hn).range := by
  change (∃ P : Point n, reverseValue K n hn P=c) ↔
    ∃ P : Point n, (scalarKummer K (reverseValue K n hn P)).toAdd=(scalarKummer K c).toAdd
  constructor
  · rintro ⟨P,rfl⟩
    exact ⟨P,rfl⟩
  · rintro ⟨P,hP⟩
    exact ⟨P,(scalarKummer K).injective (Multiplicative.toAdd.injective hP)⟩

local instance : DecidableEq ℝ := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

def realCondition (e : Side) (n : ℕ) (hn : 0<n) (c : SquareClass ℚ) : Prop :=
  occurs e ℝ (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne')
    (scalarMap ℚ (algebraMap ℚ ℝ) c)

def padicCondition (e : Side) (n : ℕ) (hn : 0<n)
    (p : ℕ) (hp : p.Prime) (c : SquareClass ℚ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  occurs e ℚ_[p] (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne')
    (scalarMap ℚ (algebraMap ℚ ℚ_[p]) c)

@[expose] def scalarSelmer (e : Side) (n : ℕ) (hn : 0<n) :=
  {c : SquareClass ℚ // realCondition e n hn c ∧
    ∀ p : ℕ, ∀ hp : p.Prime, padicCondition e n hn p hp c}

def retainedCode (e : Side) (n : ℕ) (hn : 0<n) :=
  {a : Code n // realCondition e n hn (supportedClass n a) ∧
    ∀ i : Support n, padicCondition e n hn i.val
      (Nat.prime_of_mem_primeFactors i.property) (supportedClass n a)}

/-- At an actual omitted place both local conditions are precisely
even signed valuations of the actual rational representative. -/
theorem omitted_padic_condition (e : Side) (n : ℕ) (hn : 0<n)
    (p : ℕ) (hp : p.Prime) (hout : p∉(6*n).primeFactors)
    (a : ℚ) (ha : a≠0) :
    padicCondition e n hn p hp (classOf a ha) ↔ (padicValRat p a)%2=0 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp2,hp3,hnd⟩ := outside_bad_prime_support n hn.ne' p hp hout
  have hp5 := five_le_prime_of_ne_two_three hp hp2 hp3
  have hz : (n:ZMod p)≠0 := fun h => hnd ((ZMod.natCast_eq_zero_iff n p).mp h)
  have hu : IsUnit (n:ℤ_[p]) :=
    (residue_nonzero_iff_unit _).mp (by simpa only [map_natCast] using hz)
  let u : ℚˣ := Units.mk0 a ha
  have hMap := scalarMap_on_unit ℚ (algebraMap ℚ ℚ_[p]) u
  change scalarMap ℚ (algebraMap ℚ ℚ_[p]) (classOf a ha)=
    classOf (a:ℚ_[p]) (Rat.cast_ne_zero.mpr ha) at hMap
  change occurs e ℚ_[p] (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne')
     (scalarMap ℚ (algebraMap ℚ ℚ_[p]) (classOf a ha)) ↔ _
  rw [hMap]
  cases e
  · simpa only [occurs,PadicInt.coe_natCast,Padic.valuation_ratCast] using
      (target_good_class_iff hp5 (n:ℤ_[p]) hu (a:ℚ_[p]) (Rat.cast_ne_zero.mpr ha))
  · simpa only [occurs,PadicInt.coe_natCast,Padic.valuation_ratCast] using
      (source_good_class_iff hp5 (n:ℤ_[p]) hu (a:ℚ_[p]) (Rat.cast_ne_zero.mpr ha))

/-- Every retained signed monomial has literally zero valuation
outside the specified prime factor set. -/
theorem supported_outside_valuation_zero (n : ℕ) (a : Code n)
    (p : ℕ) (hp : p.Prime) (hout : p∉(6*n).primeFactors) :
    padicValRat p (scalar n a)=0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : ∀ i : Support n, Fact i.val.Prime :=
    fun i => ⟨Nat.prime_of_mem_primeFactors i.property⟩
  let q : Support n → ℕ := fun i => i.val
  have hN : 0<(monomial q a.2 : ℚ) := by exact_mod_cast monomial_pos q a.2
  have hV : padicValNat p (monomial q a.2)=0 := by
    rw [monomial,actual_valuation_product]
    · apply Finset.sum_eq_zero
      intro i _
      have hd : p≠q i := by
        intro h
        have hi : (i : ℕ) = p := h.symm
        apply hout
        rw [← hi]
        exact i.property
      rw [padicValNat.pow,padicValNat_primes hd,mul_zero]
    · intro i
      exact pow_ne_zero _ (Fact.out : (q i).Prime).ne_zero
  change padicValRat p ((-1:ℚ)^a.1.val * (monomial q a.2:ℚ))=0
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hN.ne',
    padicValRat.pow,padicValRat.neg,padicValRat.one,mul_zero,zero_add,
    padicValRat.of_nat,hV,Int.natCast_zero]

/-- All-place scalar Selmer classes are represented by the same
literal rational signed code, using the exact local odd images. -/
theorem actual_has_retained_code (e : Side) (n : ℕ) (hn : 0<n)
    (x : scalarSelmer e n hn) : ∃ a : Code n, supportedClass n a=x.val := by
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (α:=ℚˣ) 2).range x.val
  have h : classOf (u:ℚ) u.ne_zero=x.val := by
    change (QuotientGroup.mk (Units.mk0 (u:ℚ) u.ne_zero) : SquareClass ℚ)=x.val
    have he : Units.mk0 (u:ℚ) u.ne_zero=u := by apply Units.ext; rfl
    rw [he]
    exact hu
  obtain ⟨a,ha⟩ := supported_class_of_outside_valuations n (u:ℚ) u.ne_zero
    (fun p hp hout => by
      have hv := (omitted_padic_condition e n hn p hp hout (u:ℚ) u.ne_zero).mp
        (by rw [h]; exact x.property.2 p hp)
      refine ⟨padicValRat p (u:ℚ)/2,?_⟩
      omega)
  exact ⟨a,ha.trans h⟩

/-- Retained codes are inserted into the genuine all-place scalar
group. Omitted places are not dropped: both actual local images absorb
their zero-valuation class. -/
def codeToActual (e : Side) (n : ℕ) (hn : 0<n) (a : retainedCode e n hn) :
    scalarSelmer e n hn :=
  ⟨supportedClass n a.val,a.property.1,fun p hp => by
    by_cases h : p∈(6*n).primeFactors
    · exact a.property.2 ⟨p,h⟩
    · rw [supportedClass_value]
      apply (omitted_padic_condition e n hn p hp h (scalar n a.val) (scalar_ne n a.val)).mpr
      rw [supported_outside_valuation_zero n a.val p hp h,Int.zero_emod]⟩

/-- Exact finite reduction for both directions of the isogeny on
the same selected n. This is an equivalence with all conditions,
not merely an injection or a bound on an auxiliary subgroup. -/
def actualScalarSelmerEquiv (e : Side) (n : ℕ) (hn : 0<n) :
    retainedCode e n hn ≃ scalarSelmer e n hn :=
  Equiv.ofBijective (codeToActual e n hn) ⟨by
    intro a b he
    apply Subtype.ext
    apply supportedClass_injective n
    exact congrArg Subtype.val he,by
    intro x
    obtain ⟨a,ha⟩ := actual_has_retained_code e n hn x
    have hr : realCondition e n hn (supportedClass n a) := by
      rw [ha]
      exact x.property.1
    have hp (i : Support n) : padicCondition e n hn i.val
        (Nat.prime_of_mem_primeFactors i.property) (supportedClass n a) := by
      rw [ha]
      exact x.property.2 _ _
    exact ⟨⟨a,hr,hp⟩,Subtype.ext ha⟩⟩

theorem actualScalarSelmerFinite (e : Side) (n : ℕ) (hn : 0<n) :
    Finite (scalarSelmer e n hn) := by
  letI : Finite (retainedCode e n hn) := by
    unfold retainedCode
    infer_instance
  exact Finite.of_equiv (retainedCode e n hn) (actualScalarSelmerEquiv e n hn)

end CTActualGloballyFiniteIsogenySelmer318

#print axioms CTActualGloballyFiniteIsogenySelmer318.actualScalarSelmerEquiv
#print axioms CTActualGloballyFiniteIsogenySelmer318.actualScalarSelmerFinite
