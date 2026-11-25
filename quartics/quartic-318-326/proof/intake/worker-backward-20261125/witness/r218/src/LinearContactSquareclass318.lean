module
public import SquareReflection318
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Algebra.Polynomial.RingDivision
public section
noncomputable section
namespace LinearContactSquareclass318
set_option maxHeartbeats 700000
open Polynomial
variable {F ι:Type*} [Field F] [DecidableEq ι] (a:ι→F) (ha:Function.Injective a)

/-- The actual product of distinct linear contact polynomials is squarefree. -/
theorem product_squarefree (ha:Function.Injective a) (s:Finset ι) : Squarefree (∏i∈s,(X-C (a i):F[X])) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (pairwise_coprime_X_sub_C ha hij).isRelPrime
  · intro i hi
    exact (irreducible_X_sub_C (a i)).squarefree

/-- A nonempty product of distinct contacts, with any nonzero constant twist,
is not a square even in the actual rational-function field. -/
theorem twisted_product_nonsquare (ha:Function.Injective a) (s:Finset ι) (hs:s.Nonempty) (c:F) (hc:c≠0) :
    ¬IsSquare (algebraMap F[X] (RatFunc F) (C c*∏i∈s,(X-C (a i)))) := by
  have hu:IsUnit (C c:F[X]):=isUnit_C.mpr (IsUnit.mk0 c hc)
  have hsf:Squarefree (C c*∏i∈s,(X-C (a i):F[X])):=
    squarefree_mul_iff.mpr ⟨hu.isRelPrime_left,hu.squarefree,product_squarefree a ha s⟩
  intro h
  obtain ⟨q,hq⟩:=(SquareReflection318.fraction_square_iff _).mp h
  have hqu:IsUnit q:=hsf q (by rw [hq])
  have hpu:IsUnit (C c*∏i∈s,(X-C (a i):F[X])):=hq.symm ▸ hqu.mul hqu
  obtain ⟨i,hi⟩:=hs
  have hz:Polynomial.eval (a i) (C c*∏j∈s,(X-C (a j):F[X]))=0 := by
    rw [eval_mul,eval_C,eval_prod]
    have hp:(∏j∈s,Polynomial.eval (a i) (X-C (a j):F[X]))=0 := by
      apply Finset.prod_eq_zero hi
      simp
    rw [hp,mul_zero]
  have hv:=hpu.map (Polynomial.evalRingHom (a i))
  change IsUnit (Polynomial.eval (a i) (C c*∏j∈s,(X-C (a j):F[X]))) at hv
  rw [hz] at hv
  exact not_isUnit_zero hv

/-- Literal finite contact coordinates in the Shimura coordinate t=32s.
This is not the modular j-coordinate. -/
@[expose] def contacts : Fin 4→ℚ:=![0,32,76832,-343]
theorem contacts_injective : Function.Injective contacts := by decide

/-- Arbitrary nonzero constant twists are retained; no PEL twist is guessed. -/
theorem source_squareclass_independent (s:Finset (Fin 4)) (hs:s.Nonempty)
    (c:ℚ) (hc:c≠0) :
    ¬IsSquare (algebraMap ℚ[X] (RatFunc ℚ) (C c*∏i∈s,(X-C (contacts i)))) :=
  twisted_product_nonsquare contacts contacts_injective s hs c hc
end LinearContactSquareclass318
