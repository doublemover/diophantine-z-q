module
public import OriginalSameJAllOrderGraphQuotient318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

open Algebra Polynomial

namespace OriginalSameJExactTruncatedMark318
open OriginalSameJAllOrderGraphQuotient318 (thick parameterPower testRing)

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

def evalAt (u : A) : k[X] →+* A := (Polynomial.aeval u).toRingHom

theorem eval_X (u : A) : evalAt (k:=k) u (X:k[X]) = u := Polynomial.aeval_X _

theorem eval_C (u : A) (c : k) :
    evalAt u (C c) = algebraMap k A c := Polynomial.aeval_C _ _

variable (e : A →ₐ[k] k) (u : A)
variable (hker : RingHom.ker e.toRingHom = Ideal.span (Set.singleton u))

include hker in
theorem reads_u_zero : e u = 0 := by
  change u ∈ RingHom.ker e.toRingHom
  rw [hker]
  exact Ideal.mem_span_singleton_self u

include hker in
theorem mod_u_is_constant :
    e.toRingHom.comp (evalAt (k:=k) u) = Polynomial.evalRingHom (0:k) := by
  apply Polynomial.ringHom_ext
  · intro c
    change e (evalAt u (C c)) = (C c).eval 0
    rw [eval_C, e.commutes, Polynomial.eval_C,Algebra.algebraMap_self_apply]
  · change e (evalAt u (X:k[X])) = (X:k[X]).eval 0
    rw [eval_X, reads_u_zero e u hker, Polynomial.eval_X]

include hker in
/-- Successive actual division by the chosen regular parameter.
This does not require an analytic inverse or a supplied complete chart. -/
theorem poly_remainder (m : ℕ) (a : A) :
    ∃ p : k[X], ∃ c : A, a = evalAt u p + u^m*c := by
  induction m generalizing a with
  | zero => exact ⟨0,a,by rw [map_zero,pow_zero,one_mul,zero_add]⟩
  | succ m ih =>
      have hz : e.toRingHom (a - algebraMap k A (e a)) = 0 := by
        change e (a - algebraMap k A (e a)) = 0
        rw [map_sub, e.commutes,Algebra.algebraMap_self_apply,sub_self]
      have hd : a - algebraMap k A (e a) ∈ Ideal.span (Set.singleton u) :=
        hker ▸ RingHom.mem_ker.mpr hz
      obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hd
      obtain ⟨q,c,hc⟩ := ih b
      refine ⟨C (e a) + X*q,c,?_⟩
      rw [map_add,map_mul,eval_C,eval_X,pow_succ']
      calc
        a = (a - algebraMap k A (e a)) + algebraMap k A (e a) :=
          (sub_add_cancel _ _).symm
        _ = _ := by rw [hb,hc]; ring

variable (regular : Function.Injective (fun a : A => u*a))

include hker regular in
/-- Ordinary taylor degree is detected by the exact same quotient A/u^m. -/
theorem divisible_of_actual_order (m : ℕ) (p : k[X]) (c : A)
    (hp : evalAt u p = u^m*c) : (X : k[X])^m ∣ p := by
  induction m generalizing p c with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ m ih =>
      have hz : Polynomial.evalRingHom (0:k) p = 0 := by
        rw [←mod_u_is_constant e u hker]
        change e (evalAt u p) = 0
        rw [hp,map_mul,map_pow,reads_u_zero e u hker,zero_pow (Nat.succ_ne_zero m),zero_mul]
      have hx : (X : k[X]) ∣ p := by
        have hmem := RingHom.mem_ker.mpr hz
        rw [Polynomial.ker_evalRingHom, Polynomial.C_0, sub_zero] at hmem
        exact Ideal.mem_span_singleton.mp hmem
      obtain ⟨q,hq⟩ := hx
      rw [hq,map_mul,eval_X,pow_succ',mul_assoc] at hp
      obtain ⟨r,hr⟩ := ih q c (regular hp)
      exact ⟨r,by rw [hq,hr,pow_succ',mul_assoc]⟩

def modEval (m : ℕ) : k[X] →+* A ⧸ thick u m :=
  (Ideal.Quotient.mk (thick u m)).comp (evalAt u)

theorem pow_kernel_le (m : ℕ) :
    parameterPower (A:=k) m ≤ RingHom.ker (modEval (k:=k) u m) := by
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  apply RingHom.mem_ker.mpr
  change Ideal.Quotient.mk (thick u m) (evalAt u ((X:k[X])^m)) = 0
  rw [map_pow,eval_X]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

include hker regular in
theorem mod_kernel (m : ℕ) :
    RingHom.ker (modEval (k:=k) u m) = parameterPower (A:=k) m := by
  apply le_antisymm _ (pow_kernel_le u m)
  intro p hp
  have h := RingHom.mem_ker.mp hp
  change Ideal.Quotient.mk (thick u m) (evalAt u p)=0 at h
  obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact Ideal.mem_span_singleton.mpr (divisible_of_actual_order e u hker regular m p c hc)

include hker in
theorem mod_surj (m : ℕ) : Function.Surjective (modEval (k:=k) u m) := by
  intro z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p,c,hc⟩ := poly_remainder e u hker m a
  refine ⟨p,?_⟩
  change Ideal.Quotient.mk (thick u m) (evalAt u p) = Ideal.Quotient.mk (thick u m) a
  rw [hc,map_add]
  have hx : Ideal.Quotient.mk (thick u m) (u^m)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [map_mul,hx,zero_mul,add_zero]

/-- The actual marked truncated chart. Its inverse is the UNIQUE
full retained map into the polynomial t-jet, not a matching scalar. -/
def actualTruncation (m : ℕ) : testRing (A:=k) m ≃+* A ⧸ thick u m :=
  (Ideal.quotEquivOfEq (mod_kernel e u hker regular m).symm).trans
    (RingHom.quotientKerEquivOfSurjective (mod_surj e u hker m))

theorem truncation_polynomial (m : ℕ) (p : k[X]) :
    actualTruncation e u hker regular m (Ideal.Quotient.mk (parameterPower m) p) =
      Ideal.Quotient.mk (thick u m) (evalAt u p) := by
  calc
    _ = (modEval (k:=k) u m) p := by
      rw [actualTruncation,RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
    _ = _ := rfl

def originalMark (m : ℕ) : A →+* testRing (A:=k) m :=
  (actualTruncation e u hker regular m).symm.toRingHom.comp (Ideal.Quotient.mk (thick u m))

theorem reads_all_lifted_polynomials (m : ℕ) (p : k[X]) :
    originalMark e u hker regular m (evalAt u p) =
      Ideal.Quotient.mk (parameterPower m) p := by
  apply (actualTruncation e u hker regular m).injective
  change actualTruncation e u hker regular m
    ((actualTruncation e u hker regular m).symm
      (Ideal.Quotient.mk (thick u m) (evalAt u p))) = _
  rw [RingEquiv.apply_symm_apply,truncation_polynomial]

theorem preserves_actual_parameter (m : ℕ) :
    originalMark e u hker regular m u = Ideal.Quotient.mk (parameterPower m) (X:k[X]) := by
  have h := reads_all_lifted_polynomials e u hker regular m (X:k[X])
  rwa [eval_X] at h

theorem thick_decreases {r m : ℕ} (h : r ≤ m) :
    thick u m ≤ thick u r :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow u h)

abbrev truncate {r m : ℕ} (h : r ≤ m) :
    testRing (A:=k) m →+* testRing (A:=k) r :=
  Ideal.Quotient.factor (thick_decreases (X:k[X]) h)

/-- These are actual compatible neighborhoods, not unrelated choices
of polynomial representative at each precision. -/
theorem comparison_natural {r m : ℕ} (h : r ≤ m) :
    (Ideal.Quotient.factor (thick_decreases u h)).comp
      (actualTruncation e u hker regular m).toRingHom =
      (actualTruncation e u hker regular r).toRingHom.comp (truncate (k:=k) h) := by
  apply RingHom.ext
  intro z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  change (Ideal.Quotient.factor (thick_decreases u h))
      (actualTruncation e u hker regular m (Ideal.Quotient.mk _ p)) =
    actualTruncation e u hker regular r ((truncate (k:=k) h) (Ideal.Quotient.mk _ p))
  rw [truncation_polynomial,Ideal.Quotient.factor_mk]
  change Ideal.Quotient.mk (thick u r) (evalAt u p) =
    actualTruncation e u hker regular r
      ((Ideal.Quotient.factor (thick_decreases (X:k[X]) h)) (Ideal.Quotient.mk _ p))
  rw [Ideal.Quotient.factor_mk,truncation_polynomial]

end OriginalSameJExactTruncatedMark318

#print axioms OriginalSameJExactTruncatedMark318.poly_remainder
#print axioms OriginalSameJExactTruncatedMark318.mod_kernel
#print axioms OriginalSameJExactTruncatedMark318.actualTruncation

#print axioms OriginalSameJExactTruncatedMark318.reads_all_lifted_polynomials
#print axioms OriginalSameJExactTruncatedMark318.preserves_actual_parameter
#print axioms OriginalSameJExactTruncatedMark318.comparison_natural
