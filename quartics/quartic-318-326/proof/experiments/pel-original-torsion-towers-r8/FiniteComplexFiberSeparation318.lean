module
public import IntegralCoordinateGrowth318
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Roots
public section
noncomputable section
namespace FiniteComplexFiberSeparation318
open Set Polynomial
local instance : DecidableEq ℂ := Classical.decEq _

@[expose] def weighted {n : ℕ} (t : ℂ) (w : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, w i * t^i.val

lemma weighted_eq_eval {n : ℕ} (t : ℂ) (w : Fin n → ℂ) :
    weighted t w = (Polynomial.ofFn n w).eval t := by
  classical
  simp only [weighted,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

/-- A literal polynomial-weighted coordinate sum separates ANY finite
set of complex vectors. The finite exceptional parameters are the roots
of the actual nonzero difference polynomials for distinct pairs. -/
theorem exists_weighted_injective {n : ℕ} (W : Set (Fin n → ℂ)) (hW : W.Finite) :
    ∃ t : ℂ, Set.InjOn (weighted t) W := by
  classical
  letI : Fintype W := hW.fintype
  let J := {p : W × W // p.1 ≠ p.2}
  let P (j : J) : Polynomial ℂ := Polynomial.ofFn n j.val.1.val - Polynomial.ofFn n j.val.2.val
  have hP (j : J) : P j ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact j.property (Subtype.ext (Polynomial.injective_ofFn n h))
  let B : Set ℂ := ⋃ j : J, {t | (P j).IsRoot t}
  have hB : B.Finite := Set.finite_iUnion (fun j => Polynomial.finite_setOfPred_isRoot (hP j))
  obtain ⟨t,ht⟩ := hB.exists_notMem
  refine ⟨t,?_⟩
  intro x hx y hy he
  by_contra hxy
  let j : J := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h)⟩
  apply ht
  apply Set.mem_iUnion.mpr
  refine ⟨j,?_⟩
  change (Polynomial.ofFn n x - Polynomial.ofFn n y).eval t = 0
  rw [Polynomial.eval_sub,←weighted_eq_eval,←weighted_eq_eval,he,sub_self]

/-- Literal monic equations for every affine coordinate make EVERY
base fiber finite, without a reducedness or separability assumption. -/
theorem finite_fiber {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Set (ι → ℂ)) (π : (ι → ℂ) → (κ → ℂ))
    (Q : ι → Polynomial (MvPolynomial κ ℂ)) (hm : ∀ i, (Q i).Monic)
    (hroot : ∀ w ∈ S, ∀ i, ((Q i).map (MvPolynomial.eval (π w))).IsRoot (w i))
    (v : κ → ℂ) : {w : ι → ℂ | w ∈ S ∧ π w = v}.Finite := by
  classical
  let F := {w : ι → ℂ // w ∈ S ∧ π w = v}
  let R (i : ι) := {z : ℂ // ((Q i).map (MvPolynomial.eval v)).IsRoot z}
  letI (i : ι) : Fintype (R i) :=
    (Polynomial.finite_setOfPred_isRoot (((hm i).map (MvPolynomial.eval v)).ne_zero)).fintype
  let f (w : F) : ∀ i, R i := fun i => ⟨w.val i,by
    have h := hroot w.val w.property.1 i
    simpa only [w.property.2] using h⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  letI : Finite F := Finite.of_injective f hi
  exact Set.toFinite _
end FiniteComplexFiberSeparation318
