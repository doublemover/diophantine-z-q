module
public import Contact49Growth318
public import ActualLogWeight318
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.Nat.Factorization.Basic
public section
noncomputable section
namespace EulerIndex318
open Finset

@[expose] def eulerFactor (p:ℕ) : ℝ := 1+1/(p:ℝ)
@[expose] def eulerProduct (N:ℕ) : ℝ := ∏p∈N.primeFactors,eulerFactor p

 theorem factor_ge_one (p:ℕ) : 1≤eulerFactor p := by
  unfold eulerFactor
  have h : (0:ℝ)≤1/(p:ℝ) := by positivity
  linarith

/-- The product of any finite set of primes supported on R is bounded using
the actual five small primes and the exact thirty-second-power estimate. -/
theorem finite_euler_bound (P:Finset ℕ) (hp:∀p∈P,Nat.Prime p)
    (R:ℕ) (hR:0<R) (hsupport:∀p∈P,p∣R) :
    (∏p∈P,eulerFactor p)<3*(R:ℝ)^((1:ℝ)/32) := by
  let A := P.filter (fun p => p<13)
  let B := P.filter (fun p => ¬p<13)
  have hAsub : A⊆({2,3,5,7,11}:Finset ℕ) := by
    intro p h
    obtain ⟨hpP,hp13⟩:=Finset.mem_filter.mp h
    have hprime:=hp p hpP
    interval_cases p <;> norm_num at *
  have hA : (∏p∈A,eulerFactor p)<3 := by
    have hle := Finset.prod_le_prod_of_subset_of_one_le₀ hAsub
      (fun p _ => le_trans (by norm_num) (factor_ge_one p))
      (fun p _ _ => factor_ge_one p)
    have hsmall : (∏p∈({2,3,5,7,11}:Finset ℕ),eulerFactor p)<3 := by
      norm_num [eulerFactor]
    exact hle.trans_lt hsmall
  have hB0 : 0≤∏p∈B,eulerFactor p := Finset.prod_nonneg (fun p _ => by dsimp [eulerFactor]; positivity)
  have hBp : 0<∏p∈B,eulerFactor p := Finset.prod_pos (fun p _ => lt_of_lt_of_le (by norm_num) (factor_ge_one p))
  have hprodDiv : (∏p∈B,p)∣R := Finset.prod_primes_dvd R
    (fun p h => (hp p (Finset.mem_filter.mp h).1).prime)
    (fun p h => hsupport p (Finset.mem_filter.mp h).1)
  have hprodLe : (∏p∈B,(p:ℝ))≤R := by
    simpa only [Nat.cast_prod] using
      (Nat.cast_le.mpr (Nat.le_of_dvd hR hprodDiv) : ((∏p∈B,p : ℕ):ℝ)≤(R:ℝ))
  have hpow : (∏p∈B,eulerFactor p)^32≤(R:ℝ) := by
    rw [←Finset.prod_pow]
    apply le_trans _ hprodLe
    apply Finset.prod_le_prod₀
    · intro p _; positivity
    · intro p h
      exact Contact49Growth318.euler_factor_32 p (by exact_mod_cast (show 13≤p by have := (Finset.mem_filter.mp h).2; omega))
  have hlarge : (∏p∈B,eulerFactor p)≤(R:ℝ)^((1:ℝ)/32) := by
    have h := Real.rpow_le_rpow (pow_nonneg hB0 32) hpow (show (0:ℝ)≤(32:ℝ)⁻¹ by norm_num)
    have he : ((∏p∈B,eulerFactor p)^32)^((32:ℝ)⁻¹)=∏p∈B,eulerFactor p := by
      simpa only [Nat.cast_ofNat] using Real.pow_rpow_inv_natCast (n:=32) hB0 (by norm_num)
    rw [he] at h
    simpa only [one_div] using h
  have he : (∏p∈P,eulerFactor p)=(∏p∈A,eulerFactor p)*(∏p∈B,eulerFactor p) :=
    (Finset.prod_filter_mul_prod_filter_not P (fun p => p<13) eulerFactor).symm
  rw [he]
  exact (mul_lt_mul_of_pos_right hA hBp).trans_le
    (mul_le_mul_of_nonneg_left hlarge (by norm_num))

/-- The actual Euler product over the distinct prime divisors of N. -/
theorem euler_product_bound (N R:ℕ) (hR:0<R)
    (hsupport:∀p∈N.primeFactors,p∣R) :
    eulerProduct N<3*(R:ℝ)^((1:ℝ)/32) :=
  finite_euler_bound N.primeFactors (fun p h => Nat.prime_of_mem_primeFactors h) R hR hsupport

/-- The exact actual-index normalization needed by the49/8 height producer. -/
theorem index_bound (N R t:ℕ) (C d:ℝ) (hR:0<R) (hC:0<C)
    (hsupport:∀p∈N.primeFactors,p∣R)
    (hN:(N:ℝ)≤C*(R:ℝ)^2) (ht:t≤4608*R)
    (hd:d=(N:ℝ)*t*eulerProduct N) :
    d<2^14*C*(R:ℝ)^((97:ℝ)/32) := by
  have hR0 : (0:ℝ)<R := by exact_mod_cast hR
  have htR : (t:ℝ)≤4608*(R:ℝ) := by exact_mod_cast ht
  have hNN : (0:ℝ)≤N := by positivity
  have ht0 : (0:ℝ)≤t := by positivity
  have he0 : 0≤eulerProduct N := Finset.prod_nonneg (fun p _ => by dsimp [eulerFactor]; positivity)
  have he := euler_product_bound N R hR hsupport
  have hnt : (N:ℝ)*t≤(C*(R:ℝ)^2)*(4608*(R:ℝ)) :=
    mul_le_mul hN htR ht0 (by positivity)
  have hmain : d<(C*(R:ℝ)^2)*(4608*(R:ℝ))*(3*(R:ℝ)^((1:ℝ)/32)) := by
    rw [hd]
    exact (mul_le_mul_of_nonneg_right hnt he0).trans_lt
      (mul_lt_mul_of_pos_left he (by positivity))
  have hid : (C*(R:ℝ)^2)*(4608*(R:ℝ))*(3*(R:ℝ)^((1:ℝ)/32))=
      (3*4608)*C*(R:ℝ)^((97:ℝ)/32) := by
    have heq : (R:ℝ)^2*(R:ℝ)*(R:ℝ)^((1:ℝ)/32)=(R:ℝ)^((97:ℝ)/32) := by
      rw [←pow_succ,←Real.rpow_natCast,←Real.rpow_add hR0]
      norm_num
    nlinarith only [congrArg (fun x:ℝ => 13824*C*x) heq]
  rw [hid] at hmain
  exact hmain.trans (mul_lt_mul_of_pos_right (by nlinarith only [hC] : (3*4608:ℝ)*C<2^14*C) (Real.rpow_pos_of_pos hR0 _))

/-- The same conclusion permits an upper-bound index formula, for example
when a central quotient reduces the exact index by a factor. -/
theorem index_bound_of_le (N R t:ℕ) (C d:ℝ) (hR:0<R) (hC:0<C)
    (hsupport:∀p∈N.primeFactors,p∣R)
    (hN:(N:ℝ)≤C*(R:ℝ)^2) (ht:t≤4608*R)
    (hd:d≤(N:ℝ)*t*eulerProduct N) :
    d<2^14*C*(R:ℝ)^((97:ℝ)/32) :=
  hd.trans_lt (index_bound N R t C _ hR hC hsupport hN ht rfl)

/-- The actual logarithmic weight and49/8 Jacobian bound, with the former
free index-height premise replaced by its finite Euler-product producer. -/
theorem jacobian_growth_of_index (N R t d:ℕ) (h:ℝ)
    (hR:0<R) (hN0:0<N) (hd0:0<d)
    (hsupport:∀p∈N.primeFactors,p∣R)
    (hN:(N:ℝ)≤ActualLogWeight318.C*(R:ℝ)^2) (ht:t≤4608*R)
    (hd:(d:ℝ)=(N:ℝ)*t*eulerProduct N)
    (hh:h≤2^11*(d:ℝ)^2*(Real.log (6*(d:ℝ)*N))^2) :
    h<2^65*ActualLogWeight318.C^2*(R:ℝ)^((49:ℝ)/8) := by
  exact ActualLogWeight318.actual_jacobian_growth R d N h
    (by exact_mod_cast hR) (by exact_mod_cast hd0) (by exact_mod_cast hN0)
    (index_bound N R t ActualLogWeight318.C d hR ActualLogWeight318.C_pos hsupport hN ht hd)
    hN hh

end EulerIndex318
