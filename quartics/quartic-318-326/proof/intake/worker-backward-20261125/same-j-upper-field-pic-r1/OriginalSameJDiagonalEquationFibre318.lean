module
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section
noncomputable section

open Algebra Polynomial
open scoped TensorProduct

namespace OriginalSameJDiagonalEquationFibre318

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  [Algebra k[X] A] [IsScalarTower k k[X] A]

abbrev Prod := A⊗[k]A
abbrev Fibre := A⊗[k[X]]A

abbrev χ : A := algebraMap k[X] A (X:k[X])

def coordinateDifference : Prod (k:=k) (A:=A) :=
  χ (k:=k) (A:=A)⊗ₜ[k](1:A) - (1:A)⊗ₜ[k]χ (k:=k) (A:=A)

abbrev equationIdeal : Ideal (Prod (k:=k) (A:=A)) :=
  Ideal.span (Set.singleton (coordinateDifference (k:=k) (A:=A)))

abbrev raw : Prod (k:=k) (A:=A) →ₐ[k[X]] Fibre (k:=k) (A:=A) :=
  Algebra.TensorProduct.mapOfCompatibleSMul (k[X]) k (k[X]) A A

theorem raw_reads (a b : A) :
    raw (a⊗ₜ[k]b) = a⊗ₜ[k[X]]b := rfl

theorem raw_surj : Function.Surjective (raw (k:=k) (A:=A)) :=
  Algebra.TensorProduct.mapOfCompatibleSMul_surjective (k[X]) k (k[X]) A A

theorem equation_vanishes : raw (coordinateDifference (k:=k) (A:=A)) = 0 := by
  rw [coordinateDifference,map_sub,raw_reads,raw_reads]
  exact sub_eq_zero.mpr (Algebra.TensorProduct.tmul_one_eq_one_tmul (X:k[X]))

theorem polynomial_difference_mem (p : k[X]) :
    (algebraMap k[X] A p)⊗ₜ[k](1:A) - (1:A)⊗ₜ[k](algebraMap k[X] A p) ∈
      equationIdeal (k:=k) (A:=A) := by
  let I : Ideal (Prod (k:=k) (A:=A)) := equationIdeal (k:=k) (A:=A)
  let q := Ideal.Quotient.mkₐ k I
  let l : A →ₐ[k] Prod (k:=k) (A:=A) := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[k] Prod (k:=k) (A:=A) := Algebra.TensorProduct.includeRight
  let c : k[X] →ₐ[k] A := IsScalarTower.toAlgHom k (k[X]) A
  have h : q.comp (l.comp c) = q.comp (r.comp c) := by
    apply Polynomial.algHom_ext
    change q (χ (k:=k) (A:=A)⊗ₜ[k](1:A)) = q ((1:A)⊗ₜ[k]χ (k:=k) (A:=A))
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q ((algebraMap k[X] A p)⊗ₜ[k](1:A) -
    (1:A)⊗ₜ[k](algebraMap k[X] A p)) = 0
  exact (map_sub q _ _).trans (sub_eq_zero.mpr (AlgHom.congr_fun h p))

theorem balanced_generator (p : k[X]) (a b : A) :
    (p • a)⊗ₜ[k]b - a⊗ₜ[k](p • b) ∈ equationIdeal (k:=k) (A:=A) := by
  have h := Ideal.mul_mem_right (a⊗ₜ[k]b) _ (polynomial_difference_mem (A:=A) p)
  rw [sub_mul,Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
    one_mul,one_mul,←Algebra.smul_def,←Algebra.smul_def] at h
  exact h

/-- Exact scheme theoretic fibre-product equation, not just the
vanishing locus of χ₁−χ₂ on field points. -/
theorem quotient_kernel :
    RingHom.ker (raw (k:=k) (A:=A)).toRingHom = equationIdeal (k:=k) (A:=A) := by
  apply le_antisymm
  · have h : LinearMap.ker (raw (k:=k) (A:=A)).toLinearMap ≤
        (equationIdeal (k:=k) (A:=A)).restrictScalars (k[X]) := by
      change LinearMap.ker (TensorProduct.mapOfCompatibleSMul (k[X]) k (k[X]) A A) ≤ _
      rw [TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul]
      apply Submodule.span_le.mpr
      rintro x ⟨p,a,b,rfl⟩
      exact balanced_generator p a b
    intro x hx
    exact h (show x ∈ LinearMap.ker (raw (k:=k) (A:=A)).toLinearMap from hx)
  · exact (Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr (equation_vanishes (k:=k) (A:=A)))

def quotient : (Prod (k:=k) (A:=A) ⧸ equationIdeal (k:=k) (A:=A)) ≃+*
    Fibre (k:=k) (A:=A) :=
  (Ideal.quotEquivOfEq (quotient_kernel (k:=k) (A:=A)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f:=(raw (k:=k) (A:=A)).toRingHom) raw_surj)

theorem quotient_reads (z : Prod (k:=k) (A:=A)) :
    quotient (Ideal.Quotient.mk (equationIdeal (k:=k) (A:=A)) z)=raw z := by
  calc
    _ = (raw (k:=k) (A:=A)).toRingHom z := by
      rw [quotient,RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
    _ = _ := rfl

end OriginalSameJDiagonalEquationFibre318

#print axioms OriginalSameJDiagonalEquationFibre318.quotient_kernel
#print axioms OriginalSameJDiagonalEquationFibre318.quotient_reads
