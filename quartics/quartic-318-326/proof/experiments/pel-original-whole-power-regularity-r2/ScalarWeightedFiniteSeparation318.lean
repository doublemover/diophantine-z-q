module
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Roots
public section
noncomputable section
namespace ScalarWeightedFiniteSeparation318
open Set Polynomial
variable {F T : Type*} [Field F] [Infinite F] [Field T] [Algebra F T]
local instance : DecidableEq T := Classical.decEq _

@[expose] def weighted {n : ℕ} (c : T) (w : Fin n → T) : T :=
  ∑ i : Fin n, w i * c^i.val
lemma weighted_eq_eval {n : ℕ} (c : T) (w : Fin n → T) :
    weighted c w = (Polynomial.ofFn n w).eval c := by
  classical
  simp only [weighted,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

/-- One parameter from the ACTUAL infinite constant field separates
any finite family of vectors even over a larger field. Exceptional
parameters are inverse images of finite root sets under the injective
original scalar map. -/
theorem exists_weighted_injective {n : ℕ} (W : Set (Fin n → T)) (hW : W.Finite) :
    ∃ c : F, Set.InjOn (weighted (algebraMap F T c)) W := by
  classical
  letI : Fintype W := hW.fintype
  let J := {p : W × W // p.1 ≠ p.2}
  let P (j : J) : Polynomial T := Polynomial.ofFn n j.val.1.val - Polynomial.ofFn n j.val.2.val
  have hP (j : J) : P j ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact j.property (Subtype.ext (Polynomial.injective_ofFn n h))
  let B : Set F := ⋃ j : J, (algebraMap F T) ⁻¹' {z | (P j).IsRoot z}
  have hB : B.Finite := Set.finite_iUnion fun j =>
    Set.Finite.preimage (algebraMap F T).injective.injOn
      (Polynomial.finite_setOfPred_isRoot (hP j))
  obtain ⟨c,hc⟩ := hB.exists_notMem
  refine ⟨c,?_⟩
  intro x hx y hy he
  by_contra hxy
  let j : J := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h)⟩
  apply hc
  apply Set.mem_iUnion.mpr
  refine ⟨j,?_⟩
  change (Polynomial.ofFn n x - Polynomial.ofFn n y).eval (algebraMap F T c) = 0
  rw [Polynomial.eval_sub,←weighted_eq_eval,←weighted_eq_eval,he,sub_self]
end ScalarWeightedFiniteSeparation318
