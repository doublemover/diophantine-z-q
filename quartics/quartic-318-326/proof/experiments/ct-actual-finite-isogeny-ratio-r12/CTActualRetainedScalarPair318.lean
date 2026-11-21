module
public import CTActualFiniteIsogenyLinear318
public import CTNativeRealSquareclassEquiv318
public import CTNativePadicSquareclassEquiv318
public import CTExplicitLocalBitForms318
import all CTExplicitLocalBitForms318
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import all CTActualFiniteIsogenyLinear318
import Mathlib.Tactic.Ring
public section
noncomputable section

namespace CTActualRetainedScalarPair318

open CTActualFiniteIsogenyLinear318 ActualNaturalAllPlacesFinite318
open CTNativeOddSquareclassCoordinates318 CTNativeDyadicSquareclassCoordinates318
open CTNativePadicSquareclassEquiv318 CTNativeRealSquareclassEquiv318
open CTExplicitLocalBitForms318
open ActualTwoDescentSquareClassQuotient318
open scoped BigOperators

abbrev F₂ := ZMod 2

private def bilinOfAdd {V : Type*} [AddCommGroup V] [Module F₂ V]
    (b : V → V → F₂) (hl₀ : ∀ y, b 0 y=0) (hr₀ : ∀ x, b x 0=0)
    (hl : ∀ x z y, b (x+z) y=b x y+b z y)
    (hr : ∀ x z y, b x (z+y)=b x z+b x y) : LinearMap.BilinForm F₂ V :=
  ({
    toFun x := ({
      toFun y := b x y
      map_zero' := hr₀ x
      map_add' z y := hr x z y } : V →+ F₂).toZModLinearMap 2
    map_zero' := LinearMap.ext hl₀
    map_add' x z := LinearMap.ext (hl x z)
  } : V →+ (V →ₗ[F₂] F₂)).toZModLinearMap 2

@[simp] private theorem bilinOfAdd_apply {V : Type*} [AddCommGroup V] [Module F₂ V]
    (b : V → V → F₂) (hl₀ hr₀ hl hr) (x y : V) :
    bilinOfAdd b hl₀ hr₀ hl hr x y=b x y := rfl

private def addCoordinates {K : Type} [Field K] {U : Type*} [AddCommGroup U]
    (a : SquareClass K →* Multiplicative U) : ScalarBits K →+ U where
  toFun x := (a x.toMul).toAdd
  map_zero' := congrArg Multiplicative.toAdd (map_one a)
  map_add' x y := congrArg Multiplicative.toAdd (map_mul a x.toMul y.toMul)

private theorem addCoordinates_injective {K : Type} [Field K] {U : Type*} [AddCommGroup U]
    (a : SquareClass K →* Multiplicative U) (ha : Function.Injective a) :
    Function.Injective (addCoordinates a) := by
  intro x y h
  exact Additive.toMul.injective (ha (Multiplicative.toAdd.injective h))

private theorem addCoordinates_surjective {K : Type} [Field K] {U : Type*} [AddCommGroup U]
    (a : SquareClass K →* Multiplicative U) (ha : Function.Surjective a) :
    Function.Surjective (addCoordinates a) := by
  intro u
  obtain ⟨z,hz⟩ := ha (Multiplicative.ofAdd u)
  exact ⟨Additive.ofMul z,congrArg Multiplicative.toAdd hz⟩

def realVector : ScalarBits ℝ →+ F₂ := addCoordinates coordinates

theorem realVector_class (x : ℝ) (hx : x≠0) :
    realVector (Additive.ofMul (classOf x hx))=if 0<x then 0 else 1 :=
  coordinates_on_value x hx

def realForm : LinearMap.BilinForm F₂ (ScalarBits ℝ) :=
  bilinOfAdd (fun x y => realVector x*realVector y)
    (fun y => by rw [map_zero,zero_mul])
    (fun x => by rw [map_zero,mul_zero])
    (fun x z y => by rw [map_add,add_mul])
    (fun x z y => by rw [map_add,mul_add])

theorem realForm_apply (x y : ScalarBits ℝ) : realForm x y=realVector x*realVector y := rfl

theorem realSeparates (x : ScalarBits ℝ) (h : ∀ y, realForm x y=0) : x=0 := by
  have hSur := addCoordinates_surjective coordinates coordinates_surjective
  obtain ⟨y,hy⟩ := hSur (1:F₂)
  have hV : realVector x=0 := by
    have he := h y
    rw [realForm_apply,show realVector y=1 from hy,mul_one] at he
    exact he
  apply addCoordinates_injective coordinates coordinates_injective
  change realVector x=realVector 0
  rwa [map_zero]

section Odd
variable (p : ℕ) [Fact p.Prime]

def oddVector : ScalarBits ℚ_[p] →+ F₂ × F₂ := addCoordinates (oddCoordinates p)

theorem oddVector_class (x : ℚ_[p]) (hx : x≠0) :
    oddVector p (Additive.ofMul (classOf x hx))=
      (oddCoordinates p (classOf x hx)).toAdd := rfl

def oddSign : F₂ := signBit (legendreSym p (-1))

def oddForm : LinearMap.BilinForm F₂ (ScalarBits ℚ_[p]) :=
  bilinOfAdd (fun x y => odd (oddSign p) (oddVector p x) (oddVector p y))
    (fun _ => by rw [map_zero]; simp [odd])
    (fun _ => by rw [map_zero]; simp [odd])
    (fun _ _ _ => by rw [map_add]; simp [odd] <;> ring)
    (fun _ _ _ => by rw [map_add]; simp [odd] <;> ring)

theorem oddForm_apply (x y : ScalarBits ℚ_[p]) :
    oddForm p x y=odd (oddSign p) (oddVector p x) (oddVector p y) := rfl

theorem oddSeparates (hp2 : p≠2) (x : ScalarBits ℚ_[p]) (h : ∀ y, oddForm p x y=0) : x=0 := by
  have hSur := addCoordinates_surjective (oddCoordinates p) (oddCoordinates_surjective p hp2)
  have hV := odd_nondegenerate (oddSign p) (oddVector p x) (fun t => by
    obtain ⟨y,hy⟩ := hSur t
    have he := h y
    rwa [oddForm_apply,show oddVector p y=t from hy] at he)
  apply addCoordinates_injective (oddCoordinates p) (oddCoordinates_injective p hp2)
  change oddVector p x=oddVector p 0
  rwa [map_zero]

end Odd

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def dyadicVector : ScalarBits ℚ_[2] →+ F₂ × F₂ × F₂ := addCoordinates dyadicCoordinates

theorem dyadicVector_class (x : ℚ_[2]) (hx : x≠0) :
    dyadicVector (Additive.ofMul (classOf x hx))=
      (dyadicCoordinates (classOf x hx)).toAdd := rfl

def dyadicForm : LinearMap.BilinForm F₂ (ScalarBits ℚ_[2]) :=
  bilinOfAdd (fun x y => dyadic (dyadicVector x) (dyadicVector y))
    (fun _ => by rw [map_zero]; simp [dyadic])
    (fun _ => by rw [map_zero]; simp [dyadic])
    (fun _ _ _ => by rw [map_add]; simp [dyadic] <;> ring)
    (fun _ _ _ => by rw [map_add]; simp [dyadic] <;> ring)

theorem dyadicForm_apply (x y : ScalarBits ℚ_[2]) :
    dyadicForm x y=dyadic (dyadicVector x) (dyadicVector y) := rfl

theorem dyadicSeparates (x : ScalarBits ℚ_[2]) (h : ∀ y, dyadicForm x y=0) : x=0 := by
  have hSur := addCoordinates_surjective dyadicCoordinates dyadicCoordinates_surjective
  have hV := dyadic_nondegenerate (dyadicVector x) (fun t => by
    obtain ⟨y,hy⟩ := hSur t
    have he := h y
    rwa [dyadicForm_apply,show dyadicVector y=t from hy] at he)
  apply addCoordinates_injective dyadicCoordinates dyadicCoordinates_injective
  change dyadicVector x=dyadicVector 0
  rwa [map_zero]

/-- At p=2 use the literal dyadic form; at any other p use the actual
odd valuation/unit form with κ determined by the symbol of −1. -/
def localPrimeForm (p : ℕ) [Fact p.Prime] : LinearMap.BilinForm F₂ (ScalarBits ℚ_[p]) := by
  by_cases hp : p=2
  · subst p
    exact dyadicForm
  · exact oddForm p

theorem localPrimeForm_odd (p : ℕ) [Fact p.Prime] (hp : p≠2) :
    localPrimeForm p=oddForm p := by simp [localPrimeForm,hp]

theorem localPrimeForm_two : localPrimeForm 2=dyadicForm := by simp [localPrimeForm]

theorem localPrimeSymm (p : ℕ) [Fact p.Prime] (x y : ScalarBits ℚ_[p]) :
    localPrimeForm p x y=localPrimeForm p y x := by
  by_cases hp : p=2
  · subst p
    rw [localPrimeForm_two,dyadicForm_apply,dyadicForm_apply]
    exact dyadic_symm _ _
  · rw [localPrimeForm_odd p hp,oddForm_apply,oddForm_apply]
    exact odd_symm _ _ _

theorem localPrimeSeparates (p : ℕ) [Fact p.Prime] (x : ScalarBits ℚ_[p])
    (h : ∀ y, localPrimeForm p x y=0) : x=0 := by
  by_cases hp : p=2
  · subst p
    exact dyadicSeparates x (fun y => by simpa only [localPrimeForm_two] using h y)
  · exact oddSeparates p hp x (fun y => by simpa only [localPrimeForm_odd p hp] using h y)

local instance {n : ℕ} (i : Support n) : Fact i.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors i.property⟩

/-- Exact elementary local forms, added on the same actual retained
space used by both Selmer conditions. No value at omitted primes is
substituted, and no Brauer interpretation is asserted. -/
def retainedForm (n : ℕ) : LinearMap.BilinForm F₂ (RetainedSpace n) :=
  bilinOfAdd (fun x y => realForm x.1 y.1+∑ i : Support n,localPrimeForm i.val (x.2 i) (y.2 i))
    (fun y => by simp)
    (fun x => by simp)
    (fun x z y => by
      change realForm (x.1+z.1) y.1+
        (∑ i : Support n, localPrimeForm i.val (x.2 i+z.2 i) (y.2 i))=_
      simp only [map_add,LinearMap.add_apply,Finset.sum_add_distrib]
      ring)
    (fun x z y => by
      change realForm x.1 (z.1+y.1)+
        (∑ i : Support n, localPrimeForm i.val (x.2 i) (z.2 i+y.2 i))=_
      simp only [map_add,Finset.sum_add_distrib]
      ring)

theorem retainedForm_apply (n : ℕ) (x y : RetainedSpace n) :
    retainedForm n x y=realForm x.1 y.1+∑ i : Support n,localPrimeForm i.val (x.2 i) (y.2 i) := rfl

theorem retainedForm_symm (n : ℕ) (x y : RetainedSpace n) :
    retainedForm n x y=retainedForm n y x := by
  simp only [retainedForm_apply,realForm_apply]
  rw [mul_comm (realVector x.1) (realVector y.1)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact localPrimeSymm i.val _ _

theorem retainedForm_separates (n : ℕ) (x : RetainedSpace n)
    (h : ∀ y, retainedForm n x y=0) : x=0 := by
  apply Prod.ext
  · apply realSeparates
    intro y
    simpa only [retainedForm_apply,map_zero,Pi.zero_apply,Finset.sum_const_zero,add_zero]
      using h ((y,0):RetainedSpace n)
  · funext i
    change x.2 i=0
    apply localPrimeSeparates i.val
    intro y
    let single : (j : Support n) → ScalarBits ℚ_[j.val] := Pi.single i y
    have hs : (∑ j : Support n,localPrimeForm j.val (x.2 j) (single j))=
        localPrimeForm i.val (x.2 i) y := by
      rw [Finset.sum_eq_single i]
      · rw [show single i=y by simp [single]]
      · intro j _ hji
        rw [show single j=0 by simp [single,hji], map_zero]
      · simp
    simpa only [retainedForm_apply,map_zero,zero_add,hs] using h ((0,single):RetainedSpace n)

theorem retainedForm_nondegenerate (n : ℕ) : (retainedForm n).Nondegenerate := by
  refine ⟨retainedForm_separates n,?_⟩
  intro x h
  apply retainedForm_separates n x
  intro y
  rw [retainedForm_symm]
  simpa only [LinearMap.flip_apply] using h y

end CTActualRetainedScalarPair318

#print axioms CTActualRetainedScalarPair318.retainedForm_nondegenerate
