module
public import CTActualSignedGeneratorsQR318
public import CTFiniteIsogenyOrthogonalCount318
import all CTActualFiniteIsogenyLinear318
import all CTGlobalSupportedSquareclassCode318
import all CTOriginalPrimeMonomials318
import all CTActualSignedGeneratorsQR318
import Mathlib.Tactic.NormNum
public section
noncomputable section

namespace CTActualDiagonalIsotropic318

open CTActualSignedGeneratorsQR318 CTActualPrimeScalarRows318
open CTActualFiniteIsogenyLinear318 CTActualRetainedScalarPair318
open CTFiniteIsogenyOrthogonalCount318 CTActualQuadraticHOne318
open CTGlobalSupportedSquareclassCode318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentSquareClassQuotient318 ActualNaturalAllPlacesFinite318
open LinearMap.BilinForm
open scoped BigOperators

local instance {n : ℕ} (i : Support n) : Fact i.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors i.property⟩

def signCode (n : ℕ) : Code n := (1,0)
def atPrimeCode (n : ℕ) (i : Support n) : Code n := (0,Pi.single i 1)

def signedPrimeCode (n : ℕ) : Option (Support n) → Code n
  | .none => signCode n
  | .some i => atPrimeCode n i

private theorem sign_code_scalar (n : ℕ) : scalar n (signCode n)= -1 := by
  simp [scalar,signCode,monomial,show (1:F₂).val=1 from rfl]

private theorem prime_code_scalar (n : ℕ) (i : Support n) : scalar n (atPrimeCode n i)=i.val := by
  have h : monomial (fun j : Support n => j.val) (Pi.single i (1:F₂))=i.val := by
    unfold monomial
    rw [Finset.prod_eq_single i]
    · simp only [Pi.single_eq_same,show (1:F₂).val=1 from rfl,pow_one]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  simp [scalar,atPrimeCode,h]

private theorem signed_code_class (n : ℕ) :
    supportedClass n (signCode n)=classOf (-1:ℚ) (neg_ne_zero.mpr one_ne_zero) := by
  rw [supportedClass_value]
  exact (class_of_eq_iff _ _ _ _).mpr
    ⟨1,one_ne_zero,by simpa only [one_pow,mul_one] using sign_code_scalar n⟩

private theorem prime_code_class (n : ℕ) (i : Support n) :
    supportedClass n (atPrimeCode n i)=
      classOf (i.val:ℚ) (Nat.cast_ne_zero.mpr (Fact.out : i.val.Prime).ne_zero) := by
  rw [supportedClass_value]
  exact (class_of_eq_iff _ _ _ _).mpr
    ⟨1,one_ne_zero,by simpa only [one_pow,mul_one] using prime_code_scalar n i⟩

private theorem scalar_minusOne_map (K : Type) [Field K] [CharZero K]
    (f : ℚ →+* K) :
    Additive.ofMul (scalarMap ℚ f (classOf (-1:ℚ) (neg_ne_zero.mpr one_ne_zero)))=negOneLabel K := by
  let a := Units.mk0 (-1:ℚ) (neg_ne_zero.mpr one_ne_zero)
  have h := scalarMap_on_unit ℚ f a
  apply Additive.toMul.injective
  change scalarMap ℚ f (classOf (-1:ℚ) (neg_ne_zero.mpr one_ne_zero))=
    classOf (-1:K) (neg_ne_zero.mpr one_ne_zero)
  exact h.trans ((class_of_eq_iff _ _ _ _).mpr
    ⟨1,one_ne_zero,by simp [a,map_neg,map_one]⟩)

private theorem scalar_prime_map (K : Type) [Field K] [CharZero K]
    (f : ℚ →+* K) (q : ℕ) (hq : q≠0) :
    Additive.ofMul (scalarMap ℚ f (classOf (q:ℚ) (Nat.cast_ne_zero.mpr hq)))=primeLabel K q hq := by
  let a := Units.mk0 (q:ℚ) (Nat.cast_ne_zero.mpr hq)
  have h := scalarMap_on_unit ℚ f a
  apply Additive.toMul.injective
  change scalarMap ℚ f (classOf (q:ℚ) (Nat.cast_ne_zero.mpr hq))=
    classOf (q:K) (Nat.cast_ne_zero.mpr hq)
  exact h.trans ((class_of_eq_iff _ _ _ _).mpr
    ⟨1,one_ne_zero,by simp [a,map_natCast]⟩)

theorem diag_sign_actual (n : ℕ) : diagonal n (signCode n)=minusOneTuple n := by
  apply Prod.ext
  · rw [real_diag,signed_code_class]
    exact scalar_minusOne_map ℝ _
  · funext i
    change _=(minusOneTuple n).2 i
    rw [padic_diag,signed_code_class]
    exact scalar_minusOne_map ℚ_[i.val] _

theorem diag_prime_actual (n : ℕ) (j : Support n) :
    diagonal n (atPrimeCode n j)=primeTuple n j := by
  apply Prod.ext
  · rw [real_diag,prime_code_class]
    exact scalar_prime_map ℝ _ _ _
  · funext i
    change _=(primeTuple n j).2 i
    rw [padic_diag,prime_code_class]
    exact scalar_prime_map ℚ_[i.val] _ _ _

private def signProjection (n : ℕ) : Code n →+ F₂ where
  toFun x := x.1
  map_zero' := rfl
  map_add' _ _ := rfl

private def primeProjection (n : ℕ) (i : Support n) : Code n →+ F₂ where
  toFun x := x.2 i
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Exact generator decomposition of the real sign and retained
rational exponent bits, with the same retained prime indices. -/
theorem code_decomposition (n : ℕ) (a : Code n) :
    a.1 • signCode n+(∑ i : Support n, a.2 i • atPrimeCode n i)=a := by
  apply Prod.ext
  · change signProjection n (a.1 • signCode n+∑ i : Support n, a.2 i • atPrimeCode n i)=a.1
    rw [map_add,map_sum]
    have h₁ : signProjection n (a.1 • signCode n)=a.1 := by
      change a.1*1=a.1
      rw [mul_one]
    have h₀ (i : Support n) : signProjection n (a.2 i • atPrimeCode n i)=0 := by
      change a.2 i*0=0
      rw [mul_zero]
    simp only [h₁,h₀,Finset.sum_const_zero,add_zero]
  · funext j
    change primeProjection n j (a.1 • signCode n+∑ i : Support n, a.2 i • atPrimeCode n i)=a.2 j
    rw [map_add,map_sum]
    have h₀ : primeProjection n j (a.1 • signCode n)=0 := by
      change a.1*0=0
      rw [mul_zero]
    have h₁ (i : Support n) : primeProjection n j (a.2 i • atPrimeCode n i)=
        if j=i then a.2 i else 0 := by
      change a.2 i*(Pi.single i (1:F₂) j)=_
      by_cases h : j=i
      · subst j
        simp only [Pi.single_eq_same,mul_one,if_pos rfl]
      · simp only [Pi.single_eq_of_ne h,mul_zero,if_neg h]
    simp only [h₀,h₁,zero_add]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro i _ hi
      rw [if_neg (Ne.symm hi)]
    · simp

private theorem globalDiagonal_span (n : ℕ) :
    globalDiagonal n=Submodule.span F₂ (Set.range (fun i => diagonal n (signedPrimeCode n i))) := by
  let S := Submodule.span F₂ (Set.range (fun i => diagonal n (signedPrimeCode n i)))
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    change diagonal n a∈S
    have ha := code_decomposition n a
    rw [←ha,map_add,map_smul,map_sum]
    apply S.add_mem
    · apply S.smul_mem
      exact Submodule.subset_span ⟨none,rfl⟩
    · apply Submodule.sum_mem
      intro i _
      rw [map_smul]
      apply S.smul_mem
      exact Submodule.subset_span ⟨some i,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨signedPrimeCode n i,rfl⟩

private theorem generator_pair_zero (n : ℕ) (hn : 0<n) (i j : Option (Support n)) :
    retainedForm n (diagonal n (signedPrimeCode n i)) (diagonal n (signedPrimeCode n j))=0 := by
  cases i with
  | none =>
    cases j with
    | none => simpa only [signedPrimeCode,diag_sign_actual] using qr_minus_one_self n hn
    | some q => simpa only [signedPrimeCode,diag_sign_actual,diag_prime_actual] using qr_minus_one_prime n hn q
  | some p =>
    cases j with
    | none =>
      rw [retainedForm_symm]
      simpa only [signedPrimeCode,diag_sign_actual,diag_prime_actual] using qr_minus_one_prime n hn p
    | some q =>
      by_cases h : p=q
      · subst q
        simpa only [signedPrimeCode,diag_prime_actual] using qr_prime_self n hn p
      · simpa only [signedPrimeCode,diag_prime_actual] using qr_primes_distinct n hn p q h

/-- Elementary signed rational reciprocity, now on the exact
global diagonal W of actual scalar Selmer codes. -/
theorem actual_diagonal_isotropic (n : ℕ) (hn : 0<n) :
    globalDiagonal n ≤ (retainedForm n).orthogonal (globalDiagonal n) := by
  rw [globalDiagonal_span]
  exact span_self_orthogonal_of_generators (retainedForm n) _ (generator_pair_zero n hn)

end CTActualDiagonalIsotropic318

#print axioms CTActualDiagonalIsotropic318.actual_diagonal_isotropic
