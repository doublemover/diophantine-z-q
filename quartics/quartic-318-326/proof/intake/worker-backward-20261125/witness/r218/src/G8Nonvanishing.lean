module
public import QuarticOptimization
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.FieldTheory.Minpoly.Finite
public section
namespace G8Nonvanishing
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] noncomputable def H : ℤ[X] := X^8 + C (-192270) * X^7 + C (-30806460750) * X^6 + C (-7973482203618750) * X^5 + C (-2479952302380521718750) * X^4 + C (-851465052104826626542968750) * X^3 + C (-311051252579570529422291542968750) * X^2 + C (-118580513764646775079013093468261718750) * X^1 + C (-46635290553126754318176506211428210449218750) * X^0

theorem degree_H : H.natDegree=8 := by
  unfold H
  compute_degree <;> norm_num

theorem monic_H : H.Monic := by
  unfold H
  monicity!

theorem eisenstein_H : H.IsEisensteinAt (Ideal.span ({2} : Set ℤ)) := by
  refine ⟨?_,?_,?_⟩
  · rw [monic_H.leadingCoeff,Ideal.mem_span_singleton]
    norm_num
  · intro n hn
    rw [degree_H] at hn
    interval_cases n <;> norm_num [H,Ideal.mem_span_singleton,Polynomial.coeff_add,
      Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X]
  · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton]
    norm_num [H,Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X]

theorem irreducible_H : Irreducible H := by
  apply eisenstein_H.irreducible
  · exact (Ideal.span_singleton_prime (by norm_num : (2:ℤ) ≠ 0)).mpr (by norm_num)
  · exact monic_H.isPrimitive
  · rw [degree_H]; norm_num

@[expose] noncomputable def HQ : ℚ[X] := H.map (Int.castRingHom ℚ)

theorem irreducible_HQ : Irreducible HQ :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast monic_H.isPrimitive).mp irreducible_H

theorem degree_HQ : HQ.natDegree=8 := by
  rw [HQ,monic_H.natDegree_map,degree_H]

theorem monic_HQ : HQ.Monic := monic_H.map _

theorem HQ_no_root {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (hdim : Module.finrank ℚ K < 8) (x : K) :
    aeval x HQ ≠ 0 := by
  intro hx
  have heq := minpoly.eq_of_irreducible_of_monic irreducible_HQ hx monic_HQ
  have hdeg := minpoly.natDegree_le (A := ℚ) x
  rw [←heq,degree_HQ] at hdeg
  omega

@[expose] def G8 {K : Type*} [Field K] (x : K) : K :=
    1 - (2/5)*x - (2/15)*x^2 - (14/195)*x^3 - (154/3315)*x^4 -
    (22/663)*x^5 - (418/16575)*x^6 - (9614/480675)*x^7 - (2622/160225)*x^8

theorem scaled_reverse_identity {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (x : K) (hx : x ≠ 0) :
    (aeval ((480675:K)/x) HQ)*x^8=(480675:K)^8*G8 x := by
  simp only [HQ,H,Polynomial.aeval_def,Polynomial.eval₂_map,Polynomial.eval₂_add,
    Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C]
  norm_num [G8]
  field_simp
  <;> ring

theorem G8_nonzero {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (hdim : Module.finrank ℚ K < 8) (x : K) :
    G8 x ≠ 0 := by
  intro hg
  have hx : x ≠ 0 := by intro hx; simp [hx,G8] at hg
  have hh := scaled_reverse_identity x hx
  rw [hg,mul_zero] at hh
  have he : aeval ((480675:K)/x) HQ=0 :=
    (mul_eq_zero.mp hh).resolve_right (pow_ne_zero 8 hx)
  exact HQ_no_root hdim _ he

end G8Nonvanishing
