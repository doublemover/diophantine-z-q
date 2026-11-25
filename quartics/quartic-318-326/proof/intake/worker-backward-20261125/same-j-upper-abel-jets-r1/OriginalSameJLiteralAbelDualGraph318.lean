module
public import OriginalSameJRetainedAffineJet318
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

open Algebra

namespace OriginalSameJLiteralAbelDualGraph318
open OriginalSameJRetainedAffineJet318 (Jet proj)

abbrev Dual (A : Type*) := TrivSqZeroExt A A

theorem mul_snd {T : Type*} [CommRing T] (x y : Dual T) :
    (x*y).snd = x.fst*y.snd+y.fst*x.snd := by
  simp only [TrivSqZeroExt.snd_mul, op_smul_eq_smul, smul_eq_mul]

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
variable (j : A →ₐ[k] Jet k)

def first : A →+* k := (proj (k:=k)).comp j.toRingHom

theorem first_value (x : A) : first j x = (j x).fst := rfl

theorem first_scalar (v : k) : first j (algebraMap k A v) = v := by
  change ((TrivSqZeroExt.fstHom k k k).comp j) (algebraMap k A v) = v
  exact ((TrivSqZeroExt.fstHom k k k).comp j).commutes v

/-- Actual first-order graph retraction on the product with the
dual-number test: it sends scalar ε to ε and (a,0) to this j a. -/
def graph : Dual A →+* Jet k where
  toFun x := ((j x.fst).fst, (j x.fst).snd + (j x.snd).fst)
  map_zero' := by
    apply TrivSqZeroExt.ext
    · change (j 0).fst = 0
      rw [map_zero, TrivSqZeroExt.fst_zero]
    · change (j 0).snd + (j 0).fst = 0
      simp only [map_zero, TrivSqZeroExt.snd_zero, TrivSqZeroExt.fst_zero, add_zero]
  map_one' := by
    apply TrivSqZeroExt.ext
    · change (j 1).fst = 1
      rw [map_one, TrivSqZeroExt.fst_one]
    · change (j 1).snd + (j 0).fst = 0
      simp only [map_one, map_zero, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_zero, add_zero]
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mk, TrivSqZeroExt.fst_add, map_add]
    · simp only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]
      ring
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mk, TrivSqZeroExt.fst_mul, map_mul]
    · simp only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_mk, TrivSqZeroExt.fst_mul,
        mul_snd, TrivSqZeroExt.fst_add, map_mul, map_add]
      ring

theorem actual_graph_read (x : Dual A) :
    (graph j x).fst = first j x.fst ∧
      (graph j x).snd = (j x.fst).snd + first j x.snd := ⟨rfl,rfl⟩

def equation (u : A) (v : k) : Dual A := (u,-algebraMap k A v)

theorem generator_vanishes (u : A) (v : k) (hu : j u = ((0,v) : Jet k)) :
    graph j (equation u v) = 0 := by
  apply TrivSqZeroExt.ext
  · change (j u).fst = 0
    exact congrArg TrivSqZeroExt.fst hu
  · change (j u).snd + first j (-algebraMap k A v) = 0
    rw [hu, map_neg, first_scalar]
    exact add_neg_cancel v

/-- The full scheme-theoretic graph kernel, not just its support.
One exact residue equation on the isolated sheet gives the first
order deformation of that same equation. -/
theorem whole_kernel (u : A) (v : k) (hu : j u = ((0,v) : Jet k))
    (hker : RingHom.ker (first j) = Ideal.span (Set.singleton u)) :
    RingHom.ker (graph j) = Ideal.span (Set.singleton (equation u v)) := by
  apply le_antisymm
  · intro x hx
    have hx0 := RingHom.mem_ker.mp hx
    have h1 : first j x.fst = 0 := congrArg TrivSqZeroExt.fst hx0
    have h2 : (j x.fst).snd + first j x.snd = 0 := congrArg TrivSqZeroExt.snd hx0
    have hc : x.fst ∈ Ideal.span (Set.singleton u) :=
      hker ▸ RingHom.mem_ker.mpr h1
    obtain ⟨c,hc⟩ := Ideal.mem_span_singleton'.mp hc
    have hv : (j x.fst).snd = v * first j c := by
      rw [← hc, map_mul, mul_snd, hu]
      change (j c).fst * v + 0 * (j c).snd = v * (j c).fst
      rw [zero_mul, add_zero, mul_comm]
    have hd : x.snd + algebraMap k A v * c ∈ Ideal.span (Set.singleton u) := by
      rw [← hker]
      apply RingHom.mem_ker.mpr
      rw [map_add, map_mul, first_scalar, add_comm]
      exact hv ▸ h2
    obtain ⟨d,hd⟩ := Ideal.mem_span_singleton'.mp hd
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨((c,d) : Dual A), TrivSqZeroExt.ext ?_ ?_⟩
    · exact hc
    · rw [mul_snd]
      change c * (-algebraMap k A v) + u * d = x.snd
      rw [mul_comm u d, hd]
      ring
  · apply Ideal.span_le.mpr
    intro x hx
    have he : x = equation u v := Set.mem_singleton_iff.mp hx
    subst x
    exact RingHom.mem_ker.mpr (generator_vanishes j u v hu)

theorem equation_regular (u : A) (v : k)
    (hu : Function.Injective (fun a : A => u*a)) :
    Function.Injective (fun x : Dual A => equation u v * x) := by
  intro x y h
  have h₁ : x.fst = y.fst := hu (congrArg TrivSqZeroExt.fst h)
  have h₂ := congrArg TrivSqZeroExt.snd h
  simp only [mul_snd, equation, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk] at h₂
  rw [h₁] at h₂
  exact TrivSqZeroExt.ext h₁ (hu (add_right_cancel h₂))

/-- On the actual complement where u is a unit, the positive
relative divisor O(P_ε-P) has transition 1+ε·v/u, not the inverse. -/
theorem positive_transition {T : Type*} [CommRing T] (u : Tˣ) (v : T) :
    ((u.val,-v) : Dual T) * ((1,(↑u⁻¹ : T)*v) : Dual T) =
      ((u.val,0) : Dual T) := by
  apply TrivSqZeroExt.ext
  · exact mul_one _
  · rw [mul_snd]
    change u.val * ((↑u⁻¹ : T)*v) + 1 * (-v) = 0
    rw [u.mul_inv_cancel_left, one_mul, add_neg_cancel]

end OriginalSameJLiteralAbelDualGraph318

#print axioms OriginalSameJLiteralAbelDualGraph318.whole_kernel
#print axioms OriginalSameJLiteralAbelDualGraph318.equation_regular
#print axioms OriginalSameJLiteralAbelDualGraph318.positive_transition
