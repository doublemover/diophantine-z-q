module
public import OriginalSameJAllOrderGraphQuotient318
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section
noncomputable section

open Polynomial
open scoped BigOperators

namespace OriginalSameJAllOrderPositiveGraph318
open OriginalSameJAllOrderGraphQuotient318 (thick parameterPower testRing)

variable {A : Type*} [CommRing A]

abbrev parameter (m:ℕ) : testRing (A:=A) m := Ideal.Quotient.mk (parameterPower m) X

abbrev constantImage (m:ℕ) (u:A) : testRing (A:=A) m :=
  Ideal.Quotient.mk (parameterPower m) (C u)

theorem parameter_nil (m:ℕ) : (parameter (A:=A) m)^m=0 := by
  change (Ideal.Quotient.mk (parameterPower m) (X:A[X]))^m=0
  rw [←map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- Multiplication by the ORIGINAL uniformizer's constantImage lift in
the thickened chart stays injective, even though the test is nonreduced. -/
theorem constant_cancel_zero (m:ℕ) (u:A)
    (reg : Function.Injective (fun a:A => u*a)) (z:testRing (A:=A) m)
    (hz : constantImage m u * z=0) : z=0 := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk (parameterPower m) (C u) *
    Ideal.Quotient.mk (parameterPower m) p = 0 at hz
  rw [←map_mul] at hz
  have hd : (X:A[X])^m ∣ C u*p := Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply Polynomial.X_pow_dvd_iff.mpr
  intro d dh
  have h := Polynomial.X_pow_dvd_iff.mp hd d dh
  rw [Polynomial.coeff_C_mul] at h
  apply reg
  exact h.trans (mul_zero u).symm

theorem equation_cancel_zero (m:ℕ) (u:A)
    (reg : Function.Injective (fun a:A => u*a)) (z:testRing (A:=A) m)
    (hz : (constantImage m u - parameter m)*z = 0) : z = 0 := by
  let U := constantImage m u
  let t : testRing (A:=A) m := parameter m
  have hz' : U*z=t*z := sub_eq_zero.mp ((sub_mul U t z).symm.trans hz)
  have hpow : ∀ i : ℕ, U^i*z=t^i*z := by
    intro i
    induction i with
    | zero => rfl
    | succ i hi =>
        calc
          U^(i+1)*z = U*(U^i*z) := by rw [pow_succ',mul_assoc]
          _ = U*(t^i*z) := congrArg (fun x => U*x) hi
          _ = t^i*(U*z) := mul_left_comm _ _ _
          _ = t^i*(t*z) := congrArg (fun x => t^i*x) hz'
          _ = t^(i+1)*z := by rw [pow_succ,mul_assoc]
  have he : U^m*z=0 := (hpow m).trans (by rw [parameter_nil,zero_mul])
  have cancel : ∀ i : ℕ, U^i*z=0 → z=0 := by
    intro i
    induction i with
    | zero => intro h; rwa [pow_zero,one_mul] at h
    | succ i hi =>
        intro h
        rw [pow_succ',mul_assoc] at h
        exact hi (constant_cancel_zero m u reg _ h)
  exact cancel m he

theorem positive_equation_regular (m:ℕ) (u:A)
    (reg : Function.Injective (fun a:A => u*a)) :
    Function.Injective (fun z:testRing (A:=A) m => (constantImage m u - parameter m)*z) := by
  intro x y h
  have h' : (constantImage m u - parameter m)*(x-y)=0 :=
    (mul_sub _ _ _).trans (sub_eq_zero.mpr h)
  exact sub_eq_zero.mp (equation_cancel_zero m u reg (x-y) h')

section Inverted
variable {B : Type*} [CommRing B]

/-- Exact positive overlap frame of the relative Cartier difference.
Term i is t^i/u^i; the sign is fixed by multiplication with u-t. -/
theorem positive_overlap (u:Bˣ) (t:B) (m:ℕ) (nil : t^m=0) :
    ((u:B)-t)*(∑ i ∈ Finset.range m, ((↑u⁻¹:B)*t)^i) = (u:B) := by
  let x : B := (↑u⁻¹:B)*t
  have hx : x^m=0 := by
    change ((↑u⁻¹:B)*t)^m=0
    rw [mul_pow,nil,mul_zero]
  have hs : (∑ i ∈ Finset.range m,x^i)*(1-x)=1 :=
    (geom_sum_mul_neg x m).trans (by rw [hx,sub_zero])
  have hu : (u:B)-t = (u:B)*(1-x) := by
    change (u:B)-t = (u:B)*(1-(↑u⁻¹:B)*t)
    rw [mul_sub,mul_one,u.mul_inv_cancel_left]
  change ((u:B)-t)*(∑ i ∈ Finset.range m,x^i)=(u:B)
  rw [hu,mul_assoc,mul_comm (1-x),hs,mul_one]

end Inverted
end OriginalSameJAllOrderPositiveGraph318

#print axioms OriginalSameJAllOrderPositiveGraph318.positive_equation_regular
#print axioms OriginalSameJAllOrderPositiveGraph318.positive_overlap
